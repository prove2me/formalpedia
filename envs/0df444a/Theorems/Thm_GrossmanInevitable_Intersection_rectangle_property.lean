-- Prove2me | Theorems.Thm_GrossmanInevitable_Intersection_rectangle_property
-- name    : GrossmanInevitable.Intersection.rectangle_property
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:03:33.613347+00:00
-- url     : https://prove2.me/theorems/4ccde402-e71a-405b-bfa8-cb2e3c7d5ee3
-- title:
--   §2.2 — the inputs sharing a transcript of a deterministic protocol form a rectangle
-- statement:
--   Fix a deterministic protocol $\pi$ and any input pair $(a_0,b_0)$, and let $\tau=\pi(a_0,b_0)$. Then
--   $$R_\tau=\{(a,b)\in A\times B:\ \pi(a,b)=\pi(a_0,b_0)\}$$
--   is a rectangle: $R_\tau=X\times Y$ for some $X\subseteq A$, $Y\subseteq B$.
--
--   Differences from the source:
--   - generalization: finite input domains A, B (standing assumption of §2) → arbitrary types A B : Type; reason: the rectangle property does not use finiteness; finite A, B is the special case
--   - encoding: a deterministic protocol in which the players alternately send messages whose lengths are determined by the past messages; its transcript π(a, b) and output val(π(a, b)) → the published binary protocol tree OneOfManyCC.Protocol; transcript = the list of bits along the path to the leaf, val = Protocol.eval (the leaf label); reason: the standard equivalent tree form of a deterministic protocol (each bit sent is an inner node of its sender); same transcripts, outputs and costs
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), §2.2 'Rectangles arising from deterministic protocols', p. 14 (PDF 16)

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol
import Definitions.Def_GrossmanInevitable_Intersection_Transcript

open OneOfManyCC

namespace GrossmanInevitable.Intersection

/-- **Rectangle property of transcripts** (§2.2, printed p. 14 / PDF 16): for a deterministic
protocol `π` and any input pair `(a₀, b₀)`, the set `R_τ = {(a, b) ∈ A × B : π(a, b) = π(a₀, b₀)}`
of the input pairs inducing the transcript `τ = π(a₀, b₀)` is a rectangle `X × Y`. -/
theorem rectangle_property {A B O : Type} (π : Protocol A B O) (a₀ : A) (b₀ : B) :
    IsRectangle (transcriptRect π a₀ b₀) := by sorry

end GrossmanInevitable.Intersection
