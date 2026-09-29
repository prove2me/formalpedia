-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom
-- name    : ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/df8e70d3-5e00-5287-a954-0fc0ce96d9d9
-- title:
--   Level-q functions embed in level-qℓ and are level-fixed
-- statement:
--   Let $q,M',\ell\ge 1$ be natural numbers with $q$ and $M'$ coprime, let $L$ be a field of characteristic zero and let $\xi\in L$ be a primitive $(q\ell)$-th root of unity; assume there is a ring homomorphism $\iota_0:L\to\mathbb C$ with $\iota_0(\xi)=e^{2\pi i/(q\ell)}$. Let $K$ be the intermediate field of $L\subseteq L((X))$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2M'$ with subgroup [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $(q\ell)\,M'$, the kernel of the reduction $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$. Write $L\cdot F_0$ for the corresponding field at level $q^2M'$ with subgroup the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, and let [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25) $L\,\ell$ be the ring endomorphism of $L((X))$ multiplying all exponents by $\ell$ (substitution $X\mapsto X^{\ell}$). The conclusion is twofold: first, for every $x\in L\cdot F_0$ one has $\mathrm{qExpand}(x)\in K$; second, for every such $x$, every $w\in K$ whose Laurent series is $\mathrm{qExpand}(x)$, every $\gamma\in SL_2(\mathbb Z)$ lying in both $\Gamma(q)$ and $\Gamma_0(M')$, and every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29) $L\,(q\ell)\,\xi\,(q\ell)\,((q\ell)^2M')$ for the above subgroup at $\gamma^{-1}$ — that is, $\tau$ transforms every ratio of integral $q$-expansions of weight-$k$ forms on the relevant group into the corresponding ratio of $q$-expansions of the forms slashed by the conjugate $\begin{pmatrix}a&b/(q\ell)\\ (q\ell)c&d\end{pmatrix}$ of $\gamma^{-1}$, under any embedding of $L$ in $\mathbb C$ sending $\xi$ to $e^{2\pi i/(q\ell)}$ — one has $\tau w=w$.
--
--   This is the elementary half of the identification of the image of the full-level-$q$ modular function field under $X\mapsto X^{\ell}$ with the subfield of the full-level-$q\ell$ field fixed by the level automorphisms attached to $\Gamma(q)\cap\Gamma_0(M')$: the image is contained in the larger field and is pointwise fixed, while the converse inclusion (fixed elements come from level $q$) is the Galois-theoretic content and is not asserted here. It feeds the auxiliary-level statements that convert invariance under the level automorphisms into the existence of a $q$-expansion at level $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom
    (q : ℕ) [NeZero q] (M' : ℕ) [NeZero M'] (hqM' : Nat.Coprime q M') (ℓ : ℕ) [NeZero ℓ]
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
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
      ∀ w : ↥K, ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L ℓ x →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            τ w = w) := by sorry
