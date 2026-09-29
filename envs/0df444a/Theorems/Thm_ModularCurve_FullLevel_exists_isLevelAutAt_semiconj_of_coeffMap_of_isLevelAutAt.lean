-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt
-- name    : ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/ccf0cf32-5a0b-5b79-98e4-062e2b0f8c84
-- title:
--   Coefficientwise Galois conjugation of level automorphisms at ξ
-- statement:
--   Let $L$ be a field of characteristic zero, $q$ a prime, $M'$ and $m$ nonzero natural numbers with $q \mid m$ and $\gcd(m,M')=1$, and let $\xi \in L$ be a primitive $m$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((\mathsf q))$ (Laurent series over $L$), let $\sigma$ be a ring automorphism of $L$ and $\tau$ a ring automorphism of $K$ acting coefficientwise through $\sigma$, i.e. the Laurent series of $\tau x$ is obtained from that of $x$ by applying $\sigma$ to every coefficient. Then there exists $d \in (\mathbb Z/q)^\times$ such that for every $\gamma \in \Gamma_0(M')$ and every $L$-algebra automorphism $g$ of $K$ satisfying `IsLevelAutAt L m ξ m (m^2*M') (levelH m M') γ K g` there are $\gamma' \in \Gamma_0(M')$ and an $L$-algebra automorphism $g'$ of $K$ with: $\gamma \in \Gamma(q)$ implies $\gamma' \in \Gamma(q)$; the image of $\gamma'$ in $GL_2(\mathbb Z/q)$ equals $\mathrm{diag}(1,d)\,\bar\gamma\,\mathrm{diag}(1,d)^{-1}$; $\tau(g'x) = g(\tau x)$ for all $x \in K$; and `IsLevelAutAt L m ξ m (m^2*M') (levelH m M') γ' K g'`. Here `levelH m M'` is the kernel of the reduction $(\mathbb Z/m^2M')^\times \to (\mathbb Z/m)^\times$, and the predicate `IsLevelAutAt L m ξ m N₀ H γ K h` asserts: for every weight $k \in \mathbb Z$, all modular forms $f,g_0$ of weight $k$ on the subgroup of $GL_2(\mathbb R)$ attached to $\Gamma_H(N_0)$, all integral power series $p_f,p_g$ that are the integral $\mathsf q$-expansions of $f$ and $g_0$ with the Laurent series of $p_g$ over $\mathbb Q$ nonzero, every $x \in K$ whose Laurent series is the image in $L((\mathsf q))$ of the ratio of those of $p_f$ and $p_g$, and every ring homomorphism $\iota : L \to \mathbb C$ with $\iota\xi = e^{2\pi i/m}$, one has $\iota$ applied coefficientwise to the Laurent series of $h(x)$, times the $\mathsf q$-expansion of $g_0 \mid_k \gamma^\sharp$, equal to the $\mathsf q$-expansion of $f \mid_k \gamma^\sharp$, where $\gamma^\sharp = \begin{pmatrix} a & b/m \\ mc & d\end{pmatrix}$ for $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$.
--
--   This is the compatibility of Shimura's level automorphisms with Galois conjugation of Laurent coefficients: conjugating a level automorphism by a coefficientwise Galois twist produces the level automorphism of a matrix whose reduction mod $q$ is a diagonal conjugate, the root of unity $\xi$ being unchanged. It feeds the analysis of the off-diagonal part of the linear term of the Drinfeld-chart witness in [`ModularCurve.FullLevel.AuxLevel.linearPart_offDiag_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_linearPart_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.linearPart_offDiag_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_linearPart_twoChartIntegralModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt
    (L : Type) [Field L] [CharZero L]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (m : ℕ) [NeZero m] (hqm : q ∣ m) (hmM : Nat.Coprime m M')
    (ξ : L) (hξ : IsPrimitiveRoot ξ m)
    (K : IntermediateField L (LaurentSeries L))
    (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (g : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K g →
        ∃ (γ' : SL(2, ℤ)) (g' : ↥K ≃ₐ[L] ↥K),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          (∀ x : ↥K, τ (g' x) = g (τ x)) ∧
          ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ' K g' := by sorry
