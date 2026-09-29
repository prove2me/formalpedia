-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/300a277d-ce9c-532c-9226-4476e21a8464
-- title:
--   Fixed field of level automorphisms equals the level-q field
-- statement:
--   Fix a prime $q$ with $q\ge 5$, a nonzero natural number $M'$ with $q\nmid M'$, and a prime $\ell$ with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity, and assume there is a ring homomorphism $L\to\mathbb{C}$ sending $\xi$ to $e^{2\pi i/(q\ell)}$. Let $K$ be an intermediate field of $L\subseteq\operatorname{LaurentSeries} L$ equal to [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the $q$-expansion function field of $\Gamma_H((q\ell)^2M')$, i.e. the subfield of $\operatorname{LaurentSeries} L$ generated over $L$ by the coefficientwise image of that rational function field, where $H=$ `levelH (q*ℓ) M'` is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$. Write $F_0$ for the analogous base-changed function field at level $\Gamma_{H_0}(q^2M')$ with $H_0$ the kernel of $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, and let [`ModularCurve.qExpand L ℓ`](def/ModularCurve_X0.html#L25) be the ring endomorphism of $\operatorname{LaurentSeries} L$ multiplying all exponents by $\ell$ (substitution $q\mapsto q^\ell$). The conclusion has two parts: first, `qExpand L ℓ` maps $F_0$ into $K$; second, for $w\in K$, the element $w$ is fixed by every $L$-automorphism $\tau$ of $K$ satisfying `IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') H γ⁻¹ K τ` for some $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ if and only if $w=$ `qExpand L ℓ x` for some $x\in F_0$. Here `IsLevelAutAt` asserts, for all weights $k$ and all modular forms $f,g$ of weight $k$ for $\Gamma_H((q\ell)^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g$ giving a nonzero series, and all $x\in K$ whose underlying Laurent series is the coefficientwise image of $p_f/p_g$, that for every ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$ one has $\iota(\tau x)\cdot\big(g\mid_k\,\mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}\big)^{\wedge}=\big(f\mid_k\,\mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}\big)^{\wedge}$ on $q$-expansions, where $\mathrm{conjElemN}\,m\,\gamma=\begin{pmatrix}a&b/m\\ mc&d\end{pmatrix}$ for $\gamma=\begin{pmatrix}a&b\\ c&d\end{pmatrix}$.
--
--   This identifies the image of the level-$q$ function field under the substitution $q\mapsto q^\ell$ as precisely the subfield of the level-$q\ell$ function field fixed by the level automorphisms attached to $\Gamma(q)\cap\Gamma_0(M')$, in a form valid over any characteristic-zero coefficient field carrying a suitable $(q\ell)$-th root of unity. It is used in the level-descent arguments for the auxiliary level, where the fixed field and the induced action of the level automorphisms on it are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
        ModularCurve.qExpand L ℓ x ∈ K) ∧
    (∀ w : ↥K,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            τ w = w) ↔
        ∃ x : LaurentSeries L,
          x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) ∧
          ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L ℓ x) := by sorry
