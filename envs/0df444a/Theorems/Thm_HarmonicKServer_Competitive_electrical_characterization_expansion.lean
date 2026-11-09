-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_electrical_characterization_expansion
-- name    : HarmonicKServer.Competitive.electrical_characterization_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:22.170106+00:00
-- url     : https://prove2.me/theorems/d4180316-e27d-41be-a17f-fffef8dcea87
-- title:
--   Lemma 4.1 — Electrical characterization and expansion
-- statement:
--   Let $k\ge2$ and let $Y$ consist of $k$ distinct points of an arbitrary metric space. For every real vector $a$ with $\sum_i a_i=0$, the minimum defining $E_Y(a)$ is attained. A feasible flow $F$ minimizes energy if and only if there are real voltages $h_i$ such that $d(y_i,y_j)F_{ij}=h_i-h_j$ for every $i\ne j$. For every such minimizing flow and voltage vector and every real zero-sum $b$,
--   $$E_Y(a+b)=E_Y(a)+2\sum_i b_ih_i+E_Y(b).$$
--   The statement supplies the attained minimum, its electrical characterization in both directions, and the entire quadratic expansion used by later identities. No existence or minimization fact is assumed as a hypothesis of the attainment clause.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: minimum over feasible flows → real infimum with a separate attainment conclusion; reason: zero-sum supplies have a nonempty feasible set and its energies are bounded below by zero; attainment restores the source minimum
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 6, Lemma 4.1; proof Appendix A, p. 14 (PDF p. 15) (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Lemma 4.1, printed p. 6 (PDF 7), including attainment, iff and expansion. -/
theorem electrical_characterization_expansion {k : ℕ} (hk : 2 ≤ k)
    {V : Type*} [MetricSpace V] (Y : KServer.Config k V) (hY : Function.Injective Y)
    (a : Vector k) (ha : ZeroSum a) :
    (∃ F : Flow k, Minimizing Y a F) ∧
    (∀ F : Flow k, Feasible a F → (Minimizing Y a F ↔ ∃ h : Vector k, Ohm Y F h)) ∧
    (∀ (F : Flow k) (h : Vector k), Minimizing Y a F → Ohm Y F h →
      ∀ b : Vector k, ZeroSum b →
      energy Y (fun i => a i + b i) = energy Y a + 2 * (∑ i, b i * h i) + energy Y b) := by sorry

end HarmonicKServer.Competitive
