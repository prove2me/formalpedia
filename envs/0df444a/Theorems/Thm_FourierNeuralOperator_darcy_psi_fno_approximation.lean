-- Prove2me | Theorems.Thm_FourierNeuralOperator_darcy_psi_fno_approximation
-- name    : FourierNeuralOperator.darcy_psi_fno_approximation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:40:27.70302+00:00
-- url     : https://prove2.me/theorems/9cade5cc-6f61-4613-b95e-6ec94de59506
-- title:
--   Theorem 3.5 (as proved): $\Psi$-FNO approximation of the Darcy solution operator
-- statement:
--   Let $\sigma\in C^3(\mathbb R)$ be non-linear (not affine). Let $k\in\mathbb N$ with $k>d/2+1$, $\delta\in(0,1)$, $s\ge d/2+k+\delta$, $\lambda\in(0,1)$, and let $f\in\dot H^{k-1}(\mathbb T^d)$. Let $\mathcal A^s_\lambda$ be the set of $\lambda$-coercive coefficients of Setting 3.4 and $G:\mathcal A^s_\lambda\to\dot H^1$, $a\mapsto u$, the solution operator of
--
--   $$-\nabla\cdot(a\nabla u)=f,\qquad\fint_{\mathbb T^d}u\,dx=0.$$
--
--   Then there is a constant $C>0$ such that for every integer $N\ge1$ there is a $\Psi$-FNO $\mathcal N$ with
--
--   $$\sup_{a\in\mathcal A^s_\lambda}\|G(a)-\mathcal N(a)\|_{H^1}\le CN^{-k},$$
--
--   and $\mathrm{width}(\mathcal N)\le CN^d$, $\mathrm{depth}(\mathcal N)\le C\log N$, $\mathrm{lift}(\mathcal N)\le C$.
--
--   So the Darcy solution operator is approximated to accuracy $\varepsilon$ by $\Psi$-FNOs of size $O(\varepsilon^{-d/k}\log\varepsilon^{-1})$.
--
--   **Formalization Note** Setting 3.4 asks only $k\in\mathbb N$. The proof emulates Algorithm 3.2, whose convergence (Theorem 3.3, Appendix E.1) needs $k>d/2+1$; this hypothesis is added. The constant $C$ is chosen after $f$ (the paper writes $C=C(s,\lambda,d)$, but it must depend on $f$). "Non-linear" is read as "not affine", as the proof needs $\sigma''\ne0$ somewhere. The solution is characterised by its Fourier coefficients: the bound is asserted for every $u\in\dot H^1$ solving the equation. Coefficients $a$ are taken continuous on $[0,2\pi]^d$. Depth $0$ is allowed, which is what the bound $C\log N$ forces at $N=1$.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 3.1, Setting 3.4 and Theorem 3.5, p. 16; proof in Appendix E.3, pp. 51-52, using Theorem 3.3 (p. 15) and Appendix E.1

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem darcy_psi_fno_approximation {d : ℕ} (σ : ℝ → ℝ) (hσ3 : ContDiff ℝ 3 σ)
    (hσnl : ¬ ∃ c₀ c₁ : ℝ, ∀ x, σ x = c₀ + c₁ * x)
    (k : ℕ) (hk : (d : ℝ) / 2 + 1 < k) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (s : ℝ) (hs : (d : ℝ) / 2 + k + δ ≤ s) (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (f : TorusFun d (Fin 1)) (hf : MemSobolev ((k : ℝ) - 1) f) (hf₀ : MeanZero f) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ Np : PsiFNO d (Fin 1) (Fin 1),
      (∀ a ∈ darcyCoeffSet d s δ lam, ContinuousOn a (torusBox d) →
        ∀ u, IsDarcySolution a f u →
          sobolevNorm 1 (u - Np.eval σ a) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-(k : ℝ)))) ∧
      (Np.width : ℝ) ≤ C * (N : ℝ) ^ d ∧ (Np.depth : ℝ) ≤ C * Real.log N ∧
      (Np.lift : ℝ) ≤ C := by sorry

end FourierNeuralOperator
