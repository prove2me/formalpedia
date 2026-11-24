-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_theorem_A_2
-- name    : NumInvQH.Oblique.Supplement.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:53:12.534456+00:00
-- url     : https://prove2.me/theorems/4d4481b7-bc38-4ca7-b9de-20c1ddd5296f
-- title:
--   Theorem A.2 — For complex U ∈ C^{n×p}, V ∈ C^{q×n}, E = U(VU)⁻¹V (Moore–Penrose) is idempotent, with the stated three-way descriptions of R(E) and N(E).
-- statement:
--   Let $n,p,q$ be positive integers, $U\in\mathbb C^{n\times p}$ and $V\in\mathbb C^{q\times n}$. Every inverse below is the Moore–Penrose pseudoinverse with all four Penrose equations, using the conjugate transpose. Put $E=U(VU)^{-1}V$. Then $E^2=E$ and
--   $$R(E)=R(UU^*V^*)=R(UU^*V^*V)=R(U)\cap\bigl((UU^*)^{-1}(R(U)\cap N(V))\bigr)^\perp,$$
--   $$N(E)=N(U^*V^*V)=N(UU^*V^*V)=N(V)\oplus (V^*V)^{-1}(R(U)+N(V))^\perp.$$
--   The inverse matrices act on subspaces by image. The last direct sum includes the assertion that its summands intersect only at zero. This supplies the full complex oblique-projector companion theorem, including singular matrices.
--
--   Differences from the source:
--   - encoding: complex matrices and their Moore–Penrose inverses → Fin-indexed matrices and matrices satisfying all four complex Penrose equations; reason: this retains arbitrary positive dimensions and singular matrices; Hermitian perpendicularity is explicit and all inverses act on subspaces by image
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 25, Theorem A.2

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Complex

open Matrix

namespace NumInvQH.Oblique.Supplement

/-- The complete complex statement of Theorem A.2, including directness of the kernel sum. -/
theorem theorem_A_2 {n p q : ℕ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (U : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin q) (Fin n) ℂ)
    (P : Matrix (Fin p) (Fin q) ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsComplexMoorePenrose (V * U) P)
    (hQ : IsComplexMoorePenrose (U * U.conjTranspose) Q)
    (hR : IsComplexMoorePenrose (V.conjTranspose * V) R) :
    let E := U * P * V
    let W := complexImage R (hermitianPerp (complexRange U ⊔ complexNull V))
    E * E = E ∧
    complexRange E = complexRange (U * U.conjTranspose * V.conjTranspose) ∧
    complexRange E = complexRange (U * U.conjTranspose * V.conjTranspose * V) ∧
    complexRange E = complexRange U ⊓
      hermitianPerp (complexImage Q (complexRange U ⊓ complexNull V)) ∧
    complexNull E = complexNull (U.conjTranspose * V.conjTranspose * V) ∧
    complexNull E = complexNull (U * U.conjTranspose * V.conjTranspose * V) ∧
    complexNull E = complexNull V ⊔ W ∧
    Disjoint (complexNull V) W := by sorry

end NumInvQH.Oblique.Supplement
