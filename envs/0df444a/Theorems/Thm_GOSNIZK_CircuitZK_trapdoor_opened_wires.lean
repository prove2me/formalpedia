-- Prove2me | Theorems.Thm_GOSNIZK_CircuitZK_trapdoor_opened_wires
-- name    : GOSNIZK.CircuitZK.trapdoor_opened_wires
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:36.931853+00:00
-- url     : https://prove2.me/theorems/7d8c7bd1-ce20-4f5a-9c66-913de4239e39
-- title:
--   Proof of Lemma 8, p. 15 — trapdoor-opened wires: $c_i=\mathrm{com}(w_i;r'_i)$, and simulated commitments are distributed as honest ones
-- statement:
--   Let the commitment scheme have perfect trapdoor opening and perfect trapdoor opening indistinguishability, let $(ck, tk)$ be a hiding key and let $w = (w_1, \dots, w_n) \in \{0,1\}^n$.
--
--   1. For all randomizers $r_1, \dots, r_n$, the trapdoor openings $r'_i = \mathrm{Topen}_{tk}(0, r_i, w_i)$ satisfy
--   $$\mathrm{com}(w_i; r'_i) = \mathrm{com}(0; r_i) \quad \text{for every } i.$$
--   2. If $r_1, \dots, r_n$ are independent and uniform on $R$, the vector $(\mathrm{com}(0; r_i))_{i}$ of simulated commitments has the same law as the vector $(\mathrm{com}(w_i; r_i))_{i}$ of honest commitments to $w$.
--
--   The first part says that every simulated commitment is a commitment to the true wire value; the second, that the commitments alone do not distinguish the simulation from an honest proof.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, proof of Lemma 8 (r'_i ← Topen_tk(0, r_i, w_i); "Now c_i = com(w_i; r'_i)")

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_Scheme
import Definitions.Def_GOSNIZK_CircuitZK_Circuit

namespace GOSNIZK.CircuitZK

/-- Proof of Lemma 8 (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15),
the trapdoor-opened wires. On a hiding key `(ck, tk)` and for wire values `w : Fin n → Bool`:
1. for all randomizers `r_i`, the trapdoor openings `r'_i = Topen_tk(0, r_i, w_i)` satisfy
   `com(w_i; r'_i) = com(0; r_i)` for every wire `i`;
2. with `r_1, …, r_n` independent and uniform on `R`, the vector `(com(0; r_i))_i` of simulated commitments has the
   same law as the vector `(com(w_i; r_i))_i` of honest commitments to `w`. -/
theorem trapdoor_opened_wires {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
    [Fintype R] [Nonempty R]
    (S : Scheme N R C CK XK TK Rp Pf) (hTO : S.PerfectTrapdoorOpening)
    (hTOI : S.PerfectTrapdoorOpeningIndist)
    (kt : CK × TK) (hkt : kt ∈ S.Khide.support) {n : ℕ} (w : Fin n → Bool) :
    (∀ (r : Fin n → R) (i : Fin n),
      S.com kt.1 (bit (w i)) (S.Topen kt.2 0 (r i) (bit (w i))) = S.com kt.1 0 (r i)) ∧
    (PMF.uniformOfFintype (Fin n → R)).map (fun r i => S.com kt.1 0 (r i)) =
      (PMF.uniformOfFintype (Fin n → R)).map (fun r i => S.com kt.1 (bit (w i)) (r i)) := by sorry

end GOSNIZK.CircuitZK
