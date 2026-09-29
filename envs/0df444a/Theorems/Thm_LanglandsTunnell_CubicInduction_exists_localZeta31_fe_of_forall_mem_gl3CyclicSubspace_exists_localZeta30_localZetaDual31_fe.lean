-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
-- name    : LanglandsTunnell.CubicInduction.exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/f6c5dcfd-26eb-51dd-9ced-e848f894c0b5
-- title:
--   Pointwise rational functional equation for Z₁ from Z₀
-- statement:
--   Let $p$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, let $F = \mathbb{Q}_p$ be the corresponding completion, carrying its Borel measurable structure, and write $q = \mathrm{absNorm}(p)$. Let $\psi$ be a $\mathbb{C}$-valued additive character of $F$ of exact level $n \in \mathbb{Z}$, in the sense that $\psi$ is trivial on $\{x : v(x) \le \exp n\}$ and some $x$ with $v(x) \le \exp(n+1)$ has $\psi(x) \ne 1$. Let $W : \mathrm{GL}_3(F) \to \mathbb{C}$ satisfy $W(u(x,y,z)h) = \psi^{-1}(x+y)\,W(h)$ for all upper unipotent $u(x,y,z)$ and all $h$, and be right invariant under some open subgroup of $\mathrm{GL}_3(F)$. Let $\chi : F^\times \to \mathbb{C}^\times$ be a homomorphism, $\gamma : \mathbb{C} \to \mathbb{C}$ an arbitrary function, and $g \in \mathrm{GL}_3(F)$. Then for every measure $\mu$ on $F^\times$ and every additive Haar measure $\nu$ on $F$ the following implication holds. Assume that for every $W'$ in the $\mathbb{C}$-span of the right translates of $W$ there are $Q_1, Q_2 \in \mathbb{C}[X]$ with $Q_2 \ne 0$, an integer $k$ and reals $\sigma_0, \sigma_1$ such that: the integrand of $Z_0(s, W', \chi; g) = \int_{F^\times} W'(\mathrm{diag}(a,1,1)g)\chi(a)|a|^{s-1}\,d\mu(a)$ is $\mu$-integrable for $\mathrm{Re}\,s > \sigma_0$, with $Z_0(s, W', \chi; g)\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ks}$ there; the integrand of $Z_1$ for the dual function $\widetilde{W'}(h) = W'(w_3\,{}^t h^{-1})$, the character $\chi^{-1}$ and the point $w'\,{}^t g^{-1}$ is $\mu \times \nu$-integrable for $\mathrm{Re}\,s > \sigma_1$, where $w_3$ is the long Weyl element and $w'$ the transposition of the last two coordinates; and $Z_1(1-s, \widetilde{W'}, \chi^{-1}; w'\,{}^t g^{-1})\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ks}\gamma(s)$ whenever $\mathrm{Re}(1-s) > \sigma_1$, where $Z_1(s, W'', \chi; h) = \int_{F^\times}\big(\int_F W''(\mathrm{diag}(a,1,1)\,u_{21}(x)\,h)\,d\nu(x)\big)\chi(a)|a|^{s-1}\,d\mu(a)$ with $u_{21}(x)$ the lower unipotent matrix of $(2,1)$-entry $x$. Then there are $Q_1, Q_2 \in \mathbb{C}[X]$ with $Q_2 \ne 0$, an integer $k$ and reals $\sigma_0, \sigma_1$ such that the integrand of $Z_1(s, W, \chi; g)$ is $\mu \times \nu$-integrable for $\mathrm{Re}\,s > \sigma_0$ with $Z_1(s, W, \chi; g)\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ks}$ there, the integrand of $Z_0(s, \widetilde{W}, \chi^{-1}; w'\,{}^t g^{-1})$ is $\mu$-integrable for $\mathrm{Re}\,s > \sigma_1$, and for $\mathrm{Re}(1-s) > \sigma_1$ one has $q^{n}\,\nu(\{x : v(x) \le 1\})^2\,Z_0(1-s, \widetilde{W}, \chi^{-1}; w'\,{}^t g^{-1})\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ks}\gamma(s)$.
--
--   This is the pointwise rational form of the passage from the $j=0$ to the $j=1$ local zeta integral in the theory of $\mathrm{GL}_3 \times \mathrm{GL}_1$ local zeta integrals of Jacquet, Piatetski-Shapiro and Shalika, the factor $\gamma$ being carried along unchanged up to the explicit constant $q^{n}\nu(\mathcal{O})^2$ coming from the level of $\psi$ and the Fourier transform of the indicator of a ball. It feeds the construction of the primal and dual middle data for the local Rankin–Selberg integrals used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
    (p : HeightOneSpectrum (𝓞 ℚ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (n : ℤ)
    (hψn : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ⁻¹ W)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (γ : ℂ → ℂ) (g : LocalGL3 p) :
    letI := localBorel ℚ p
    ∀ (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ W' ∈ gl3CyclicSubspace W, ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p μ W' χ g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p μ W' χ s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p μ ν (dualWhittakerFn3 W') χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p μ ν W' χ (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
                γ s)) →
      ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta31ConvergentAbove p μ ν W χ g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta31 p μ ν W χ s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
          IsLocalZeta30ConvergentAbove p μ (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            (Ideal.absNorm p.asIdeal : ℂ) ^ n *
                  ((ν.real {x : p.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 *
                localZeta30 p μ (dualWhittakerFn3 W) χ⁻¹ (1 - s) (weylPrime3 * transposeInv3 g) *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
                γ s) := by sorry
