-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime
-- name    : ModularCurve.FullLevel.AuxLevel.mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/5487f093-6086-50f1-a161-6edf8555b86b
-- title:
--   Valuation subring invariance under level automorphisms fixing its centre
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be distinct primes, neither dividing a nonzero natural number $M'$, let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity admitting a ring homomorphism $\iota_0\colon L\to\mathbb C$ with $\iota_0(\xi)=e^{2\pi i/(q\ell)}$, and let $K$ be the intermediate field of $L((\mathrm q))$ obtained by adjoining to $L$ the image, under coefficientwise extension of scalars, of the $q$-expansion field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2M'$ and subgroup [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $(q\ell)\,M'$, the kernel of the reduction $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$. Let $A$ be a commutative ring acting on $K$, let $j\in K$, $\varpi\in A$, write $C=$ `chartAlgFin` $A\,K\,j$ for the integral closure of $A[j]$ in $K$, let $y\subseteq C$ be an ideal containing the image of $\varpi$, let $B$ be an $A$-subalgebra of $K$ with $C\le B$, and let $W$ be a valuation subring of $K$ with $B\subseteq W$. Assume: (LOC) $f\in W$ iff $fh=g$ for some $g,h\in B$ with $h\notin\mathfrak m_W$; (CEN) for $b\in C$, $b\in y$ iff $b\in\mathfrak m_W$; (PRES), (STAB) every $L$-algebra automorphism $\tau$ of $K$ that is a level automorphism at $\gamma^{-1}$ for some $\gamma\in\Gamma_0(M')$ maps $C$ into $C$ and $B$ into $B$; (LEAST) every prime ideal $Q$ of $B$ containing the image of $\varpi$ and satisfying $Q\cap C=y$ contains $\mathfrak m_W\cap B$. Here $\tau$ being a level automorphism at $\gamma^{-1}$ (the predicate [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29) with parameters $n=m=q\ell$, $N_0=(q\ell)^2M'$, $H=$ `levelH`) means: for every weight $k$, all modular forms $f,g$ for $\Gamma_H((q\ell)^2M')$ of weight $k$ with integral $q$-expansions $p_f,p_g$, $p_g\neq 0$, every $x\in K$ whose Laurent expansion is $p_f/p_g$, and every $\iota\colon L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, the series $\iota$-applied to $\tau x$ times the $q$-expansion of $g\mid_k\!\bigl(\begin{smallmatrix}a&b/(q\ell)\\ (q\ell)c&d\end{smallmatrix}\bigr)$ equals that of $f\mid_k\!\bigl(\begin{smallmatrix}a&b/(q\ell)\\ (q\ell)c&d\end{smallmatrix}\bigr)$, where $\gamma^{-1}=\bigl(\begin{smallmatrix}a&b\\ c&d\end{smallmatrix}\bigr)$. The conclusion: for every $\gamma\in\Gamma_0(M')$ and every such level automorphism $\tau$ at $\gamma^{-1}$, if $\tau$ preserves $y$ in the sense that $b\in y\iff\tau b\in y$ for all $b\in C$ with $\tau b\in C$, then $f\in W\iff\tau f\in W$ for all $f\in K$.
--
--   In the intended geometric situation $B$ is the coordinate ring of an affine open of a blow-up of the $j$-finite chart of a model of the modular curve at a supersingular point $y$ of the special fibre, and $W$ is the valuation ring of the unique exceptional component above $y$, so the assertion is that the stabiliser of $y$ among the level automorphisms coming from $\Gamma_0(M')$ lies in the decomposition group of that component. It is used in the decomposition of the Drinfeld fibre of the blown-up chart under the level action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [Algebra A ↥K] (j : ↥K) (ϖ : A)
    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (B : Subalgebra A ↥K) (W : ValuationSubring ↥K)
    (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hloc : ∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K))

    (hcen : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
      ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W)

    (hpres : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)

    (hstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ f : ↥K, f ∈ B → τ f ∈ B)

    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
      (∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ Q) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
            b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
        ∀ f : ↥K, f ∈ W ↔ τ f ∈ W := by sorry
