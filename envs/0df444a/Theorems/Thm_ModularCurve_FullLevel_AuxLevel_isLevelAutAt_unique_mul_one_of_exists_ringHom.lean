-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/fe7b3b4b-4d5d-5eec-ba9d-cb271a3d7e99
-- title:
--   Level automorphisms over Γ₀(M'): uniqueness, composition, triviality
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'\ge 1$ with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $q\ell$-th root of unity, and assume there is a ring homomorphism $\iota_0:L\to\mathbb{C}$ with $\iota_0(\xi)=e^{2\pi i/(q\ell)}$. Let $K$ be the intermediate field of $L\subseteq\operatorname{LaurentSeries} L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image under $\mathbb{Q}\to L$ of the rational $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $N_0=(q\ell)^2M'$ and group $H=\ker\bigl((\mathbb{Z}/N_0)^\times\to(\mathbb{Z}/q\ell)^\times\bigr)$. Say that an $L$-algebra automorphism $\tau$ of $K$ is a level automorphism at $\gamma\in SL(2,\mathbb{Z})$ when, for every weight $k$, all weight-$k$ modular forms $f,g$ for [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) $N_0\,H$ with integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[X]]$, $p_g$ giving a nonzero Laurent series, every $x\in K$ whose underlying Laurent series is the image of $p_f/p_g$, and every ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, one has $\iota(\tau x)\cdot q\text{-}\exp(g\mid_k\gamma^\sharp)=q\text{-}\exp(f\mid_k\gamma^\sharp)$, where $\gamma^\sharp=\begin{pmatrix}a&b/(q\ell)\\ (q\ell)c&d\end{pmatrix}$ for $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}$. The conclusion is threefold: for $\gamma\in\Gamma_0(M')$ any two level automorphisms at $\gamma$ coincide; for $\gamma,\delta\in\Gamma_0(M')$ with $\tau$ a level automorphism at $\gamma$ and $\sigma$ one at $\delta$, the product $\tau\sigma$ in the automorphism group is a level automorphism at $\delta\gamma$ (so the assignment is contravariant); and the identity is a level automorphism at every $\gamma\in\Gamma(q\ell)\cap\Gamma_0(M')$.
--
--   These three assertions are the group-theoretic input showing that the level automorphisms attached to elements of $\Gamma_0(M')$ form an action of $\Gamma_0(M')/(\Gamma(q\ell)\cap\Gamma_0(M'))$ on the level-$q\ell$ function field, the deck transformations of the covering of modular curves $X(\Gamma(q\ell)\cap\Gamma_0(M'))\to X_0(M')$ read on function fields. They are used in the subsequent analysis of the blow-up charts and of the stability of level structures under this action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ τ' : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K τ' →
      τ = τ') ∧

    (∀ γ δ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → δ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') δ K σ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') (δ * γ) K (τ * σ)) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma (q * ℓ) → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K 1) := by sorry
