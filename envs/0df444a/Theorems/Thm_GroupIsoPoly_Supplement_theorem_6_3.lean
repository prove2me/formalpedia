-- Prove2me | Theorems.Thm_GroupIsoPoly_Supplement_theorem_6_3
-- name    : GroupIsoPoly.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:30:19.830393+00:00
-- url     : https://prove2.me/theorems/7f251eb1-27ff-43e9-988b-e201101f18b1
-- title:
--   Theorem 6.3, p.49 — $(T/J(T))^D=0$ and $H^1(D,T/J(T))=0$ for cubic tensor modules of stable classical groups
-- statement:
--   Let $K$ be a finite field of characteristic $p$ and let $D=\prod_{i<t}G_i$ be a product of derived classical groups $\mathrm{SL}$, $\mathrm{Sp}$, $\mathrm{SU}$, $\Omega$ over the common defining field $K$, in their natural representations and in the stable range (natural dimension $\ge64$, Witt index $\ge32$ for symplectic, unitary and orthogonal factors). Let
--
--   $$T=T_1\otimes_K T_2\otimes_K T_3,$$
--
--   where each $T_k$ is a natural, dual, or Frobenius-twisted module of one factor of $D$, and let $J(T)$ be its pairing submodule (Definition 16). Then
--
--   $$\big(T/J(T)\big)^D=0,\qquad H^1\big(D,T/J(T)\big)=0 .$$
--
--   These assertions hold
--
--   1. with fixed multiplicities: for $(T/J(T))\otimes_K K^m$, every $m$;
--   2. for every central-product image $\bar D$ of $D$, given by a surjection $D\to\bar D$ with central kernel through which the action on $T/J(T)$ factors;
--   3. after prime-field descent: for the prime-field tensor module $T'=T_1'\otimes_{\mathbb F_p}T_2'\otimes_{\mathbb F_p}T_3'$, where $T_k'$ is $T_k$ viewed over $\mathbb F_p$, and its pairing submodule $J(T')$ formed over $\mathbb F_p$.
--
--   Consequently every 1-cocycle $c:D\to T/J(T)$ equals $c(g)=(g-1)b$ for a unique $b\in T/J(T)$, and for any generating set $S$ of $D$ this $b$ is the unique solution of the linear equations $(s-1)b=c(s)$, $s\in S$.
--
--   In the paper this removes the affine obstruction in cubic tensor modules: after quotienting by invariant pairings, an affine action can be moved to a linear one by a computable change of origin.
--
--   **Formalization Note** The conclusions are packaged in `QuotCohVanishes`, asserted over $K$ and over $\mathbb F_p$ for every matrix realization of the restricted modules. Factors may repeat and the $T_k$ may come from different factors.
--
--   Differences from the source:
--   - reading: "each Ti is a natural, dual, or Frobenius-twisted module of one factor" → Frobenius twists of the natural and of the dual module are both allowed; reason: Definition 16 does not restrict the twist; Theorem 6.1(iv) says "a Frobenius twist of either"; the broader reading is the stronger statement, and the prime-field descent clause involves Galois twists of duals anyway
--   - reading: "The assertions hold after prime-field descent" → for every F_p-matrix realization T'_k of the restriction of scalars of T_k to F_p, the same conclusions for T' = T'_1 ⊗_{F_p} T'_2 ⊗_{F_p} T'_3 and its pairing submodule J(T') formed over F_p; reason: Theorem 6.2 applies its assertions to "a prime-field tensor module"; the other reading (T/J(T) viewed over F_p) is clause 1 itself, since fixed vectors and cocycles do not depend on the scalar field
--   - reading: "with fixed multiplicities" → (T/J(T)) ⊗ F^m for every m ≥ 0, i.e. m copies; reason: multiplicity spaces carry the trivial action
--   - reading: "for a central-product image given with its quotient map" → every surjective φ : D → D̄ with ker φ ≤ Z(D) such that ker φ acts trivially on T/J(T): H¹(D̄, T/J(T)) = 0; reason: the image must act on T/J(T); its fixed vectors are those of D since φ is onto
--   - reading: "a unique b … computable by solving these linear equations on generators" → b is unique modulo J and, for every generating set S of D, every solution of (s−1)b′ = c(s) (s ∈ S) equals b modulo J; reason: no running time is claimed; the content is that the generator equations determine b
--   - encoding: T/J(T), T = T_1 ⊗_K T_2 ⊗_K T_3 → coordinate arrays modulo the submodule J(T); cocycles and coboundaries as congruences modulo J; reason: a function to the quotient always lifts; same instances
--   - encoding: J(T) = im J_T → span of the insertions κ_{i,η}(v), η ∈ B_i; reason: J_T is linear and P(T) is spanned by pure tensors v ⊗ η
--   - encoding: D a product of derived classical groups in the stable range → D = ∏ classicalGroup (dat i) over the common field K: SL, Sp(A), SU(σ, H), Ω(Q) = [O(Q), O(Q)] in their natural representations with any nondegenerate Gram data, n_i ≥ 64 and Witt index ≥ 32 (IsStableDerived); reason: §6.1 and Remark 1; Ω(Q) = [O(Q), O(Q)] is the paper's identification in the stable range
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 6.3, p.49 (PDF p.53); hypotheses of Theorem 6.2 and Definition 16, p.48 (PDF p.52); stable range, §6.1 and Remark 1, p.45 (PDF p.49)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_IsStableDerived
import Definitions.Def_GroupIsoPoly_Supplement_factorMat
import Definitions.Def_GroupIsoPoly_Supplement_QuotCohVanishes

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

/-- **Theorem 6.3 (Cohomology after quotienting by invariant pairings).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 6.3, p.49 (PDF p.53): "Let D and T satisfy the
hypotheses of Theorem 6.2. Then (T/J(T))^D = 0, H1(D, T/J(T)) = 0. The assertions hold after
prime-field descent, with fixed multiplicities, and for a central-product image given with its
quotient map. Consequently a cocycle c : D → T/J(T) specified by its values on the generators has a
unique b ∈ T/J(T) with c(g) = (g − 1)b, computable by solving these linear equations on generators."
The hypotheses of Theorem 6.2 (p.48, PDF p.52) are those of Definition 16 with "D a product of
classical derived groups in the stable range above" (§6.1, Remark 1, p.45).

Let `K` be a finite field of characteristic `p`, and `D = ∏_{i<t} G_i` a product of derived classical
groups `G_i ∈ {SL, Sp, SU, Ω}` over the common defining field `K`, each in its natural representation
on `K^{n_i}` and in the stable range. Let `T = T₁ ⊗_K T₂ ⊗_K T₃` where `T_k` is the natural, dual or
Frobenius-twisted module (of kind `κ k`) of the factor `f k`. Then:
1. over `K`, `QuotCohVanishes` holds for `T/J(T)`: `(T/J(T))^D = 0`, `H¹(D, T/J(T)) = 0`, both with
   every multiplicity, the unique coboundary solution `b` is the unique solution of the equations on
   any generating set, and `H¹` vanishes for every central-product image;
2. after **prime-field descent**: for any matrix realizations `ρ k` over `F_p` of the restrictions of
   scalars of `T_k` to `F_p`, the same holds for the prime-field tensor module
   `T' = T'₁ ⊗_{F_p} T'₂ ⊗_{F_p} T'₃` and its pairing submodule `J(T')` formed over `F_p`.

**Formalization Note.** Factors may repeat and the `T_k` may belong to different factors. A twist of
the dual module is allowed. See `QuotCohVanishes` for the encoding of the quotient. -/
theorem theorem_6_3 (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]
    {t : ℕ} (n : Fin t → ℕ) (dat : (i : Fin t) → ClassicalDatum K (n i))
    (hst : ∀ i, IsStableDerived (dat i)) (f : Fin 3 → Fin t) (κ : Fin 3 → ModKind) :
    QuotCohVanishes (F := K) (factorMat (K := fun _ => K) dat (f 0) (κ 0))
        (factorMat (K := fun _ => K) dat (f 1) (κ 1))
        (factorMat (K := fun _ => K) dat (f 2) (κ 2)) ∧
      ∀ (a : Fin 3 → ℕ)
        (ρ : (k : Fin 3) → ClProd (K := fun _ => K) dat → Matrix (Fin (a k)) (Fin (a k)) (ZMod p)),
        (∀ k, IsRestrictionOf (K := fun _ => K) dat (f k) (κ k) (ρ k)) →
        QuotCohVanishes (ρ 0) (ρ 1) (ρ 2) := by sorry

end Supplement

end GroupIsoPoly
