-- Prove2me | Theorems.Thm_GOSNIZK_CircuitZK_one_query
-- name    : GOSNIZK.CircuitZK.one_query
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:43.913439+00:00
-- url     : https://prove2.me/theorems/7d988389-c975-4024-841d-513d7d832e5e
-- title:
--   Proof of Lemma 8, p. 15 — one simulated proof $S_2(ck,tk,C)$ has the law of an honest proof $P(ck,C,w)$
-- statement:
--   Let the message space have order $N \ge 4$, and let the commitment scheme be homomorphic, with perfect trapdoor opening, perfect trapdoor opening indistinguishability and perfect witness indistinguishability. For every hiding key $(ck, tk)$, every NAND circuit $C$ and every witness $w$ with $C(w) = 1$,
--   $$P(ck, C, w) \overset{d}{=} S_2(ck, tk, C),$$
--   that is, an honest proof of Figure 3 and a simulated proof have the same law.
--
--   This is the core of the proof of Lemma 8: a single proof reveals nothing about the witness. Perfect zero-knowledge against adaptive adversaries making many queries follows from it.
--
--   **Formalization Note** The bound $N \ge 4$ is the paper's standing assumption for Figure 3 (p. 14); the statement does not use it beyond that.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, proof of Lemma 8 (unnumbered: one simulated proof is distributed as an honest proof)

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_Protocol

namespace GOSNIZK.CircuitZK

/-- Proof of Lemma 8 (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15), one
query. Let the message space have order `N ≥ 4` and let the scheme be homomorphic, with perfect trapdoor opening,
perfect trapdoor opening indistinguishability and perfect witness indistinguishability. On every hiding key
`(ck, tk)`, for every NAND circuit `Γ` and every witness `w` with `Γ(w) = 1`, the honest proof `P(ck, Γ, w)` of
Figure 3 and the simulated proof `S₂(ck, tk, Γ)` have the same law. -/
theorem one_query {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
    [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp] (hN : 4 ≤ N)
    (S : Scheme N R C CK XK TK Rp Pf) (hhom : S.Homomorphic) (hTO : S.PerfectTrapdoorOpening)
    (hTOI : S.PerfectTrapdoorOpeningIndist) (hWI : S.PerfectWI)
    (kt : CK × TK) (hkt : kt ∈ S.Khide.support) {n : ℕ} (Γ : Circuit n) (w : Fin n → Bool)
    (hw : Γ.Sat w) :
    prove S kt.1 Γ w = simulate S kt.1 kt.2 Γ := by sorry

end GOSNIZK.CircuitZK
