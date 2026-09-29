-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/62944a5f-6d73-5490-8823-1c919e415dc9
-- title:
--   Level automorphisms preserve the localised valuation subring
-- statement:
--   Fix a prime $q$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity, and assume there is a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\zeta) = e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K \subseteq L(\!(\mathrm{q})\!)$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion field of $\Gamma_{H_1}(q^2M')$. Let $A$ be a commutative ring acting on $K$, $j \in K$, $\varpi \in A$, let $C =$ `chartAlgFin A K j` be the subalgebra of elements of $K$ integral over $A[j]$, and let $y \subseteq C$ be an ideal containing the image of $\varpi$. Let $B$ be an $A$-subalgebra of $K$ with $C \le B$ and $B$ contained in a valuation subring $W$ of $K$, such that: $W$ consists exactly of the fractions $g/h$ with $g,h \in B$ and $h \notin \mathfrak{m}_W$ (hypothesis `hloc`); $y$ is the contraction of $\mathfrak{m}_W$ to $C$ (`hcen`); every $L$-automorphism $\tau$ of $K$ satisfying `IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ` for some $\gamma \in \Gamma_0(M')$ maps $C$ into $C$ and $B$ into $B$; and $\mathfrak{m}_W \cap B$ is least among the primes $Q$ of $B$ that contain the image of $\varpi$ and contract to $y$ on $C$ (`hleast`). Here `IsLevelAutAt` asserts that $\tau$ is characterised on elements $x$ of $K$ presented as ratios of integral $q$-expansions of weight-$k$ modular forms $f, g$ for $\Gamma_{H_1}(q^2M')$ by the identity, after any $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, $\iota(\tau x) \cdot (g \mid_k \mathrm{M}) = f \mid_k \mathrm{M}$ of $q$-expansions, with $\mathrm{M} =$ `conjElemN q γ⁻¹` the matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ built from $\gamma^{-1} = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$. The conclusion: for every $\gamma \in \Gamma_0(M')$ and every such $\tau$ attached to $\gamma^{-1}$, if $\tau$ preserves $y$ in the sense that $b \in y \iff \tau b \in y$ for all $b \in C$ with $\tau b \in C$, then $f \in W \iff \tau f \in W$ for every $f \in K$.
--
--   This is the decomposition-group step for the auxiliary rigidifying level: an automorphism of the $q$-expansion function field that fixes the centre $y$ of a chart also fixes the valuation subring obtained by localising an intermediate order $B$ there, so that the stabiliser of a point of the special fibre acts on the exceptional valuation ring above it. It feeds the decomposition of the blow-up chart of the Drinfeld fibre under level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [Algebra A ↥K] (j : ↥K) (ϖ : A)
    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (B : Subalgebra A ↥K) (W : ValuationSubring ↥K)
    (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hloc : ∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K))

    (hcen : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
      ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W)

    (hpres : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)

    (hstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∀ f : ↥K, f ∈ B → τ f ∈ B)

    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
      (∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ Q) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
            b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
        ∀ f : ↥K, f ∈ W ↔ τ f ∈ W := by sorry
