-- Prove2me | Theorems.Thm_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
-- name    : M4aHerbrand.ideleClass_herbrandQuotient_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/2abab5cd-bb6c-5c08-90b7-5bf1f8232010
-- title:
--   First inequality: Herbrand quotient of the idele class group
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an algebra over $E$ such that $F/E$ is Galois with cyclic Galois group $F \simeq_{\mathrm{alg}[E]} F$, let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_F$, $E$, $F$ — that is, a monoid homomorphism $\mathrm{act}$ from $\mathrm{Gal}(F/E)$ to the ring automorphisms of the adele ring $\mathrm{AdeleRing}(\mathcal{O}_F, F)$, each $\mathrm{act}\,g$ being continuous and satisfying $\mathrm{act}\,g\,(\iota x) = \iota(g x)$ for $x \in F$, where $\iota$ is the structural map $F \to \mathrm{AdeleRing}(\mathcal{O}_F, F)$ — and let $\sigma$ be an element of $\mathrm{Gal}(F/E)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$. Write $C_F = (\mathrm{AdeleRing}(\mathcal{O}_F, F))^{\times} / \mathrm{principalIdeles}$ for the idele class group, on which $D$ induces an action of $\mathrm{Gal}(F/E)$ by group automorphisms; let $N = \mathtt{ideleClassNorm}\,D$ be the endomorphism $c \mapsto \prod_{\tau} \tau \cdot c$ of $C_F$ and $d = \mathtt{ideleClassDerive}\,D\,\sigma$ the endomorphism $c \mapsto (\sigma \cdot c)\,c^{-1}$. Then the cardinality of $\ker d / \mathrm{im}\,N$ equals $[F:E] = \mathrm{finrank}_E F$ times the cardinality of $\ker N / \mathrm{im}\,d$, and the latter cardinality is nonzero, i.e. $\ker N / \mathrm{im}\,d$ is finite.
--
--   This is the first inequality of global class field theory in its Herbrand-quotient form: for a cyclic extension $F/E$ the Tate cohomology of the idele class group satisfies $\#\hat H^0(C_F) = [F:E]\cdot\#\hat H^{-1}(C_F)$ with $\hat H^{-1}(C_F)$ finite, so that both groups are finite and the Herbrand quotient is the degree. It is the computational input to the statements that $\hat H^{-1}(C_F)$ vanishes and $\#\hat H^0(C_F) = [F:E]$ for cyclic (in particular prime-order) Galois groups, and to the norm-kernel identity $\ker N = \mathrm{im}\,d$ on $C_F$. The existence of a descent datum $D$ is not asserted here; its uniqueness is recorded separately in [`M4aHerbrand.subsingleton_ideleGaloisDescent`](thm.html#M4aHerbrand.subsingleton_ideleGaloisDescent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand

theorem M4aHerbrand.ideleClass_herbrandQuotient_eq_finrank
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (σ : F ≃ₐ[E] F) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card ((ideleClassDerive D σ).ker ⧸
      ((ideleClassNorm D).range.subgroupOf (ideleClassDerive D σ).ker)) =
    Module.finrank E F *
    Nat.card ((ideleClassNorm D).ker ⧸
      ((ideleClassDerive D σ).range.subgroupOf (ideleClassNorm D).ker)) ∧
    Nat.card ((ideleClassNorm D).ker ⧸
      ((ideleClassDerive D σ).range.subgroupOf (ideleClassNorm D).ker)) ≠ 0 := by sorry
