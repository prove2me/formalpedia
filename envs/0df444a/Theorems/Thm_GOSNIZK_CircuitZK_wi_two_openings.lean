-- Prove2me | Theorems.Thm_GOSNIZK_CircuitZK_wi_two_openings
-- name    : GOSNIZK.CircuitZK.wi_two_openings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:22.534004+00:00
-- url     : https://prove2.me/theorems/2759abf2-6832-4eaa-a806-10232339b3ae
-- title:
--   Proof of Lemma 8, p. 15 — 0/1 proofs from any two 0/1 openings of the same commitment have the same law
-- statement:
--   Let the commitment scheme have perfect trapdoor opening and perfect witness indistinguishability, and let $(ck, tk)$ be a hiding key. If a commitment has two openings $(m, r)$ and $(m', r')$ with $m, m' \in \{0, 1\}$,
--   $$\mathrm{com}(m; r) = \mathrm{com}(m'; r'),$$
--   then the 0/1 proofs $P_{01}(ck, m, r; \rho)$ and $P_{01}(ck, m', r'; \rho)$, with $\rho$ uniform on $R_{\mathrm{proof}}$, have the same law.
--
--   Perfect witness indistinguishability is stated for the openings $m = 0$, $m' = 1$ only; this extends it to two openings with the same message, which is what comparing a simulated proof with an honest one requires.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, proof of Lemma 8 ("By the perfect witness indistinguishability of the proofs ..."); p. 7, Perfect witness indistinguishability

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_Scheme

namespace GOSNIZK.CircuitZK

/-- Proof of Lemma 8 (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15),
witness indistinguishability of the simulated proofs. On a hiding key `(ck, tk)`, if a commitment has two openings
`(m, r)` and `(m', r')` with `m, m' ∈ {0, 1}`, then the 0/1 proofs `P01(ck, m, r; ρ)` and `P01(ck, m', r'; ρ)`, with
`ρ` uniform on `R_proof`, have the same law. This extends the perfect witness indistinguishability of p. 7, stated
for `m = 0, m' = 1`, to any two 0/1 openings. -/
theorem wi_two_openings {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
    [Fintype Rp] [Nonempty Rp]
    (S : Scheme N R C CK XK TK Rp Pf) (hTO : S.PerfectTrapdoorOpening) (hWI : S.PerfectWI)
    (kt : CK × TK) (hkt : kt ∈ S.Khide.support) (m m' : ZMod N) (hm : m = 0 ∨ m = 1)
    (hm' : m' = 0 ∨ m' = 1) (r r' : R) (h : S.com kt.1 m r = S.com kt.1 m' r') :
    (PMF.uniformOfFintype Rp).map (S.P01 kt.1 m r) = (PMF.uniformOfFintype Rp).map (S.P01 kt.1 m' r') := by sorry

end GOSNIZK.CircuitZK
