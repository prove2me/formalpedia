-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_three
-- name    : ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/96f164e7-7094-5590-9f23-43ed1d74d39a
-- title:
--   Level automorphisms attached to Γ₀(M'), case q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\ge 1$ be an integer not divisible by $q$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\neq q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $\{q\ell\}$, and let $\xi\in L$ be a primitive $q\ell$-th root of unity. Write $H=\mathrm{levelH}\,(q\ell)\,M'$ for the kernel of the reduction map $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, and let $K$ be the intermediate field of $L\subset L((T))$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q}\to L$ of the $q$-expansion function field $\mathrm{xHFunctionField}\,((q\ell)^2M')\,H\subset\mathbb{Q}((T))$, i.e. $K=\mathrm{laurentBaseChange}$ of that field. The assertion is that for every $\gamma\in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M')$ there exists an $L$-algebra automorphism $\tau$ of $K$ satisfying $\mathrm{IsLevelAutAt}\,L\,(q\ell)\,\xi\,(q\ell)\,((q\ell)^2M')\,H\,\gamma^{-1}\,K\,\tau$: for every weight $k\in\mathbb{Z}$, all modular forms $f,g$ of weight $k$ on the image of $H$ in $SL(2,\mathbb{Z})$ viewed inside $GL(2,\mathbb{R})$, all integral power series $p_f,p_g$ whose images in $\mathbb{C}[[T]]$ are the width-one $q$-expansions of $f$ and $g$, with the Laurent series attached to $p_g$ over $\mathbb{Q}$ nonzero, every $x\in K$ whose image in $L((T))$ is the coefficientwise image of the quotient of the Laurent series of $p_f$ by that of $p_g$, and every ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, one has, as Laurent series over $\mathbb{C}$, $$\iota_*(\tau x)\cdot \mathrm{qExp}\bigl(g\mid_k \gamma^{-1,\sharp}\bigr)=\mathrm{qExp}\bigl(f\mid_k \gamma^{-1,\sharp}\bigr),$$ where $\gamma^{-1,\sharp}=\mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}=\mathrm{diag}(q\ell,1)^{-1}\gamma^{-1}\mathrm{diag}(q\ell,1)$.
--
--   This is the $q=3$ instance of the existence of the level automorphisms of the base-changed modular function field $L\cdot F(\Gamma_H((q\ell)^2M'))$ realising the action of $\Gamma_0(M')$ in Shimura's description of the function fields of modular curves. It is used in the study of the group of such automorphisms and of the corresponding fixed-field and divisibility criteria for membership in the base-changed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ := by sorry
