-- Prove2me | Theorems.Thm_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log
-- name    : MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/dfc5352a-ed5d-5abf-ac4e-1c9825a0f057
-- title:
--   V-basis with variable structure constants from a functional-equation logarithm
-- statement:
--   Fix a prime $p$ and an integer $d$, and write $A = \mathbb{Z}_p[X_{(m,i,j)} : (m,i,j) \in \mathbb{N}\times\mathrm{Fin}\,d\times\mathrm{Fin}\,d]$ and $K = \mathbb{Q}_p[X_{(m,i,j)}]$ for the corresponding polynomial rings. Let $\Phi_0$ be a $d$-dimensional formal group law over $A$ (a $d$-tuple of power series in two blocks of $d$ variables with vanishing constant term, linear part the identity in each block, and associative), assumed commutative. Let $a : \mathbb{N} \to M_d(K)$ and $f : \mathrm{Fin}\,d \to K[[x_1,\dots,x_d]]$ satisfy: $a_0 = 1$; for every $k$, $p\,a_{k+1} = \sum_{m=0}^{k} V_m \cdot \sigma^{m+1}(a_{k-m})$, where $V_m$ is the matrix with $(i,j)$-entry $X_{(m,i,j)}$ and $\sigma$ is the entrywise application of the $K$-algebra endomorphism $X_v \mapsto X_v^p$; the coefficient of $x_j^{p^k}$ in $f_i$ is $(a_k)_{ij}$, and all coefficients of $f_i$ at monomials not of the form $x_j^{p^k}$ vanish; and each $f_i$ is a logarithm for the base change of $\Phi_0$ along $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$ (coefficientwise on polynomials), that is, $f_i(\Phi_0(x,y)) = f_i(x) + f_i(y)$. The conclusion asserts the existence of $\gamma : \mathrm{Fin}\,d \to \mathrm{CartierModule}\;p\;\Phi_0$ — each $\gamma_i$ being a $d$-tuple of power series in countably many variables, with zero constant term, carrying the Witt addition law to $\Phi_0$ — such that the determinant of the $d \times d$ matrix whose $(i,k)$-entry is the $k$-th tangent coordinate of $\gamma_i$ (the coefficient of the first variable to the power one) is a unit in $A$, and such that for every $i$ and every $N$ there is an element $h$ of the Cartier module with
--   $$F\gamma_i = \sum_{m<N} V^{m}\Bigl(\sum_{j} \langle X_{(m,j,i)}\rangle \gamma_j\Bigr) + V^{N} h,$$
--   where $F$ is `frobenius`, $V$ is `verschiebungInt`, and $\langle c \rangle$ denotes `homothety` by $c \in A$; note the index order $(m,j,i)$, so the structure constant of $F\gamma_i$ at $\gamma_j$ is the $(j,i)$-entry of the variable matrix $V_m$.
--
--   This is the curve-theoretic read-out of a functional-equation logarithm in Hazewinkel's form: the coordinate $p$-typical curves of a law whose rationalisation has logarithm given by the universal recursion constitute a $V$-basis of its Cartier module whose Frobenius structure constants are the polynomial variables themselves, congruences being checked modulo every power of $V$. It feeds the construction of the universal $p$-typical law with prescribed Cartier-module presentation, being used by [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X), where the index order $(m,i,j)$ is restored by base change along the variable swap.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) [Φ₀.IsComm]
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (h5 : ∀ i : Fin d,
      MvPowerSeries.subst (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀).toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) :
    ∃ (γ : Fin d → MvFormalGroup.CartierModule p Φ₀),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (γ i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ₀,
        MvFormalGroup.CartierModule.frobenius (γ i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety
              (MvPolynomial.X ((m : ℕ), j, i) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) (γ j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[N] h := by sorry
