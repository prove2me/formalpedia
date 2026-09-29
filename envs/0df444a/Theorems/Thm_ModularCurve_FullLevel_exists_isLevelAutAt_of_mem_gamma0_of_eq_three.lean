-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_three
-- name    : ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/9fcf15c4-0d3b-5c7f-9d1d-cea4b70f80bc
-- title:
--   Level automorphisms at q=3 for Γ₀(M')
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number with $q \nmid M'$, let $L$ be a field of characteristic zero and $\zeta \in L$ a primitive $q$-th root of unity. Let $H = \mathrm{levelH}\ q\ M'$ be the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\ L$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field of $X_H(q^2M')$, i.e. of $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ (\mathrm{GammaH}\ (q^2M')\ H)$ inside $\mathrm{LaurentSeries}\ \mathbb{Q}$. The assertion is that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ there is an $L$-algebra automorphism $\tau$ of $K$ satisfying $\mathrm{IsLevelAutAt}\ L\ q\ \zeta\ q\ (q^2M')\ H\ \gamma^{-1}\ K\ \tau$: that is, for every weight $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ for $\mathrm{GammaH}\ (q^2M')\ H$ (viewed in $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansions at $1$ come from integral power series $p_f, p_g$ with the Laurent series attached to $p_g$ over $\mathbb{Q}$ nonzero, every $x \in K$ whose underlying Laurent series is the image of the ratio of those two rational Laurent series, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, one has
--   $$\iota_*\big(\tau x\big)\cdot \mathrm{qExp}_1\big(g \mid_k \gamma^{\sharp}\big) = \mathrm{qExp}_1\big(f \mid_k \gamma^{\sharp}\big),$$
--   where $\iota_*$ is coefficientwise application of $\iota$ and $\gamma^{\sharp} = \mathrm{conjElemN}\ q\ \gamma^{-1}$ is the real matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ built from the entries $a,b,c,d$ of $\gamma^{-1}$.
--
--   This is the $q = 3$ instance of the existence of the level automorphism attached to $\gamma \in \Gamma_0(M')$ on the $q$-expansion function field of $X_H(q^2M')$ base-changed to $L$, characterised by its effect on ratios of $q$-expansions of forms of level $\Gamma_H(q^2M')$ after slashing by the conjugate $\gamma^{\sharp}$ of $\gamma^{-1}$ by $\mathrm{diag}(q,1)$. It supplies the automorphisms used in [`ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three), on the branch of the argument analysing the covering of the cusp $\infty$ at $q = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∃ τ : ↥K ≃ₐ[L] ↥K,
        ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K τ := by sorry
