-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/f00982aa-36da-5ba3-ad7c-6187652a0af0
-- title:
--   Identity level automorphism forces d_γ ≡ 1 (mod ℓ_g)
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $M' \geq 1$ satisfy $q \nmid M'$, and let $\ell_g \mid M'$. Let $L$ be a field of characteristic $0$ containing a primitive $q$-th root of unity $\xi$, and assume there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/q)$. Let $H_1 \leq (\mathbb{Z}/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$; thus $H_1$ consists of the units that are $\equiv 1$ modulo $q$ and modulo $\ell_g$. Let $K$ be the intermediate field of $\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $\mathbb{Q}$-rational $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79) of $\Gamma_{H_1}(q^2M')$. The assertion is: for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma(q)$ and in $\Gamma_0(M')$, if the identity automorphism of $K$ satisfies [`ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K 1`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — that is, for every weight $k \in \mathbb{Z}$, all modular forms $f,g$ of weight $k$ on [`CohCarrier.GammaH (q ^ 2 * M') H₁`](def/CohCarrier_Level.html#L133) with integral $q$-expansions $p_f,p_g$, with the Laurent series of $p_g$ over $\mathbb{Q}$ nonzero, and every $x \in K$ whose underlying Laurent series is the coefficientwise image of the quotient of those of $p_f$ and $p_g$, and every $\iota : L \to \mathbb{C}$ sending $\xi$ to $\exp(2\pi i/q)$, one has $\iota_*(x) \cdot (g \mid_k \gamma^\sharp)^\wedge = (f \mid_k \gamma^\sharp)^\wedge$ as Laurent series over $\mathbb{C}$, where $\gamma^\sharp$ is the matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ of `conjElemN q γ` and $(\cdot)^\wedge$ denotes the $q$-expansion — then the lower-right entry $d$ of $\gamma$ satisfies $d \equiv 1$ in $\mathbb{Z}/\ell_g$.
--
--   This is the faithfulness (converse) half of the attachment of level automorphisms to matrices in $\Gamma(q) \cap \Gamma_0(M')$: only those $\gamma$ whose lower-right entry is $\equiv 1$ modulo $\ell_g$ can induce the identity on the function field of the curve guarded by the $\Gamma_1(\ell_g)$-condition, so that the diamond operators $\langle d \rangle$ act faithfully there. It is used in the computation of the order of the stabiliser of a moduli place inside the group of level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K 1 →
      ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by sorry
