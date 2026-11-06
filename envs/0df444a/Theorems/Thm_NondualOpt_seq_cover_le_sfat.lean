-- Prove2me | Theorems.Thm_NondualOpt_seq_cover_le_sfat
-- name    : NondualOpt.seq_cover_le_sfat
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:24.997619+00:00
-- url     : https://prove2.me/theorems/0feecfd7-565d-4109-92f6-265125a32bdd
-- title:
--   Sequential covering numbers are bounded by $\mathrm{sfat}$ (RST15a, Cor. 1, as used in Theorem 6)
-- statement:
--   There are universal constants $C,c,\gamma>0$ such that for every set $Z$, every class $G$ of functions $Z\to[-1,1]$, every depth $n\ge1$ and every $0<\beta\le1$,
--   $$
--   \log N^{\mathrm{seq}}_\infty(\beta,G,n)\le C\,\mathrm{sfat}_{c\beta}(G)\,\log^\gamma\!\Big(\frac{en}\beta\Big).
--   $$
--   This is the bound of sequential covering numbers by the sequential fat-shattering dimension (Rakhlin, Sridharan and Tewari, RST15a, Corollary 1), in the form step ④ of the proof of Theorem 6 consumes. It converts the entropy integral of Proposition 20 into the sfat integral of Theorem 6.
--
--   Differences from the source:
--   - reading: "the bound of sequential covering numbers by sfat_{cβ} from (RST15a, Corollary 1)" (cited, not stated in the paper) → ∃ universal C, c, γ > 0: log N^seq_∞(β, G, n) ≤ C · sfat_{cβ}(G) · log^γ(en/β) for classes with values in [−1, 1], n ≥ 1, 0 < β ≤ 1; reason: the form in which step ④ uses it, with constants left existential
--   - encoding: sfat, log N → values in [0, ∞]; reason: sfat = ∞ makes the right side ∞
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, proof of Theorem 6, step ④, p.24; Definition 17 context, p.23

import Mathlib
import Definitions.Def_NondualOpt_sfat
import Definitions.Def_NondualOpt_seqCoverNum
import Definitions.Def_NondualOpt_logN

open scoped ENNReal

universe u

namespace NondualOpt

/-- **Sequential covering numbers are controlled by `sfat`** (the bound of (RST15a, Corollary 1),
as used in step ④ of the proof of Theorem 6). There are universal constants `C, c, γ > 0` such that
for every class `G` of functions with values in `[−1, 1]`, every depth `n ≥ 1` and every
`0 < β ≤ 1`, `log N^seq_∞(β, G, n) ≤ C · sfat_{cβ}(G) · log^γ(en/β)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, proof of Theorem 6, step ④, p.24 ("the
bound of sequential covering numbers by `sfat_{cβ}` from (RST15a, Corollary 1)"), and p.23.

**Formalization Note.** The cited bound is stated in the form step ④ consumes, with existential
universal constants chosen before the domain `Z` and the class. Values in `ℝ≥0∞`
(`sfat = ∞` makes the right side `∞`). -/
theorem seq_cover_le_sfat :
    ∃ C c γ : ℝ, 0 < C ∧ 0 < c ∧ 0 < γ ∧ ∀ (Z : Type u) (G : Set (Z → ℝ)),
      (∀ h ∈ G, ∀ z, |h z| ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ β : ℝ, 0 < β → β ≤ 1 →
        logN (seqCoverNum G β n) ≤
          ENNReal.ofReal C * (sfat G (c * β) : ℝ≥0∞) *
            ENNReal.ofReal (Real.log (Real.exp 1 * n / β) ^ γ) := by sorry

end NondualOpt
