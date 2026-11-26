-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_auxiliaryReadoutsOfCertificates
-- name    : IntMul.Kappa.DeferredReadout.auxiliaryReadoutsOfCertificates
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:26:40.435983+00:00
-- url     : https://prove2.me/theorems/c1691773-8225-47f6-94da-56fdacfa0c7d
-- title:
--   Nested certified frames give chronological absorption for deferred auxiliary edge projectors
-- statement:
--   Let $U_1,\ldots,U_k$ be the rational frames of an ordered list of deferred readouts, with every event referring to a valid frame. Suppose $U_i\subseteq U_j$ for $i<j$ and that every frame has a checked certificate for representing the coordinate-sum functional under $9G=9I-J$. Then each frame is nondegenerate for $G$. For its orthogonal projector $\pi_i$ and the rank-one formula $P_t$ of the target, define $A_i=I-(I-\pi_i)\otimes P_t$. The resulting 529-dimensional auxiliary edge projectors satisfy
--   $$A_jA_i=A_i\qquad(i<j).$$
--   The theorem applies to either round-seven schedule after its finite hypotheses are supplied. The target formula is total and yields zero on an isotropic direction.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L112-L148; deferred auxiliary edge in the October 20 round-seven mission discussion, comment 3c67b3da-c539-424c-a18d-e54c1884706e.

import Definitions.Def_IntMul_Kappa_DeferredReadoutProjectors

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.auxiliaryReadoutsOfCertificates (d : Block) (cert : Nat → GramCertificate) (es : List Event) (t : V)
    (hg : ∀ i, i < d.frames.size → (cert i).ok d.entry (d.basis i) = true)
    (hb : ∀ e ∈ es, e.frame < d.frames.size)
    (hn : (es.map d.atEvent).Pairwise (· ≤ ·)) :
    (∀ U ∈ es.map d.atEvent, IsCompl U (gramForm.orthogonal U)) ∧
    (readoutEdges (es.map d.atEvent) t).Pairwise (fun earlier later => later * earlier = earlier) := by sorry
