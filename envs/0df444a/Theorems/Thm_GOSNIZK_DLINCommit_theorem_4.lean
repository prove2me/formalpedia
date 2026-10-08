-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_theorem_4
-- name    : GOSNIZK.DLINCommit.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:07.68714+00:00
-- url     : https://prove2.me/theorems/a8f7269d-5787-4c80-94ab-a5418224f705
-- title:
--   Theorem 4 (exact part) — the DLIN commitment of Figure 2 is a homomorphic proof commitment with perfect extraction and perfect non-erasure WI
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group: $p$ prime, $\mathbb G$ and $\mathbb G_T$ of order $p$, $e$ bilinear, $g$ a generator of $\mathbb G$ and $e(g, g)$ a generator of $\mathbb G_T$. The commitment scheme of Figure 2 (keys $ck = (f, h, u, v, w)$, commitment $\mathrm{com}(m; r, s) = (u^m f^r, v^m h^s, w^m g^{r+s})$, extractor, trapdoor opening and 0/1 proof $(P_{01}, V_{01})$) has all the following properties:
--
--   1. it is homomorphic on every key of either kind;
--   2. it is perfectly binding on every binding key;
--   3. it has perfect extractability: $\mathrm{Ext}_{xk}(\mathrm{com}(m; r, s)) = m$ for $m \in \{0,1\}$;
--   4. it has perfect trapdoor opening and perfect trapdoor opening indistinguishability on every hiding key;
--   5. the 0/1 proof is perfectly complete on every key of either kind;
--   6. it is perfectly sound on every binding key: if $V_{01}(ck, c, \pi)$ accepts then $c = \mathrm{com}(m; r, s)$ for some $m \in \{0,1\}$;
--   7. it is perfectly witness indistinguishable and, with the randomness simulator
--   $$S_{01}(0, (r_0, s_0), (r_1, s_1), t) = t + r_0 s_1 - s_0 r_1$$
--   (and the inverse map when the proof was made with the opening to $1$), perfectly non-erasure witness indistinguishable on every hiding key.
--
--   Together with key indistinguishability under the decisional linear assumption, which is not part of this statement, these are the properties that make the scheme a homomorphic proof commitment in the sense of §3, the building block of the NIZK proofs and arguments for Circuit SAT in Sections 6 and 7.
--
--   **Formalization Note** (i) The paper's theorem reads "if the decision linear assumption holds for $\mathcal G_{\mathrm{DLIN}}$"; that assumption is used only for key indistinguishability, which is dropped. (ii) Each "for all adversaries, probability 1 (0)" is stated for every key in the support of the generator and every adversarial choice, and each "equal probabilities" as equality of distributions; for these perfect properties this is equivalent. (iii) The paper asks for some polynomial-time simulator for non-erasure WI; the statement names the simulator its proof constructs. (iv) $P_{01}$ carries the corrected signs of $t$ in $\pi_{12}$ and $\pi_{21}$; with the printed signs completeness is false. (v) The §3 requirement that the message space have order at least 3 holds exactly when $p \ge 3$ and is not part of the statement; all listed properties hold for every prime $p$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 11, Theorem 4 (proof pp. 11–13; Figure 2, p. 12; definitions §3, pp. 7–8)

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Theorem 4 (p. 11), exact part: the protocol of Figure 2 (with the corrected prover `P01`) is
homomorphic, perfectly binding, perfectly extractable, has perfect trapdoor opening and perfect trapdoor
opening indistinguishability, is perfectly complete and perfectly sound, perfectly witness
indistinguishable and perfectly non-erasure witness indistinguishable with the simulator `S01`. Key
indistinguishability (the decisional linear assumption) is not part of the statement. -/
theorem theorem_4 (S : DLINSetup G GT) :
    S.Homomorphic ∧ S.PerfectBinding ∧ S.PerfectExtractability ∧ S.PerfectTrapdoorOpening ∧
      S.PerfectTrapdoorOpeningIndist ∧ S.PerfectCompleteness ∧ S.PerfectSoundness ∧ S.PerfectWI ∧
      S.PerfectNonErasureWI S.S01 := by sorry

end GOSNIZK.DLINCommit
