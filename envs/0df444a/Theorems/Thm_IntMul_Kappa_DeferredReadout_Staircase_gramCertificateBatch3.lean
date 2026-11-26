-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch3
-- name    : IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch3
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:57:36.560972+00:00
-- url     : https://prove2.me/theorems/a1916e32-0be5-4f9c-995c-2fa441b83aaa
-- title:
--   Staircase witness Gram certificates for frames 624–935
-- statement:
--   Each frozen staircase frame with index 624 through 935 has an integral certificate of nondegeneracy for the rational form $G=I-J/9$. For a frame $U$, the certificate gives an integral linear combination $w$ of its generators and a positive integer $d$ such that $9G(u,w)=d\sum_j u_j$ for each generator $u$. These certificates allow construction of the true $G$-orthogonal projectors used by the deferred readouts. Frame numbering is zero-based in the published staircase data.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L112-L148; deferred auxiliary edge in the October 20, 2026 round-seven mission discussion (comment 3c67b3da-c539-424c-a18d-e54c1884706e).

import Definitions.Def_IntMul_Kappa_DeferredReadoutProjectors
import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch3 (i : Nat) (hlo : 624 ≤ i) (hhi : i < 936) :
    ∃ c : GramCertificate, c.ok Staircase.schedule.entry (Staircase.schedule.basis i) = true := by sorry
