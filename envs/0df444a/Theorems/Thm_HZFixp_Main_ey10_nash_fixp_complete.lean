-- Prove2me | Theorems.Thm_HZFixp_Main_ey10_nash_fixp_complete
-- name    : HZFixp.Main.ey10_nash_fixp_complete
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:13.055874+00:00
-- url     : https://prove2.me/theorems/203b54c4-c6d7-4038-a3cc-a66a700c34bb
-- title:
--   [EY10] (cited in §2) — three-player Nash equilibrium is FIXP-complete
-- statement:
--   Let **Nash** be the search problem whose instances are three-player games with rational payoffs (binary) and whose solutions are their mixed Nash equilibria (Definition 2.3). Then
--   $$\text{Nash is FIXP-complete under separable linear reductions:}\quad \text{Nash} \in \mathrm{FIXP} \ \text{ and every problem in FIXP SL-reduces to Nash.}$$
--
--   The paper cites this result of Etessami and Yannakakis (2010) without proof; it is the source of all hardness in the chain Nash → Quadratic Fixed Point → Reciprocal VI → HZ Equilibrium.
--
--   Differences from the source:
--   - reading: FIXP over a cube (Definition 2.4) → InFIXP via the published basicFIXP over nonempty bounded rational polytopes; reason: Definition 2.4 is attributed to [EY10], whose FIXP is defined over such polytopes; [EY10] show the cube gives the same class
--   - encoding: polynomial time (in the binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime over fixed injective encodings into the alphabet Sym (published FixpReciprocal_SLReduces); reason: the paper names no machine model; the reused FIXP framework fixes this one
--   - encoding: a three-player game in binary; solutions mixed profiles → NashInst: [m_1,m_2,m_3] and three payoff tables (lexicographic profiles), binary; solution vectors of the m_1+m_2+m_3 probabilities, player 1 first; reason: Lean convention for the instances and real solution vectors of a search problem
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 5 (PDF 7), paragraph after Definition 2.4, citing [EY10]

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_HZFixp_Main_NashProblem

open FixpReciprocal

namespace HZFixp.Main

/-- **[EY10], cited in §2 (after Definition 2.4).** Computing a three-player Nash equilibrium is
FIXP-complete under separable linear reductions. -/
theorem ey10_nash_fixp_complete : FIXPComplete nashProblem := by sorry

end HZFixp.Main
