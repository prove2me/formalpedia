-- Prove2me | Theorems.Thm_MCPoise_lemma_2_5
-- name    : MCPoise.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:21.720811+00:00
-- url     : https://prove2.me/theorems/70637f4c-ca3f-4ccd-ba51-b91907ff279f
-- title:
--   Lemma 2.5 — at most $|D'|/2$ pairs are discarded by Algorithm 1
-- statement:
--   Let $(x, f, \lambda)$ be feasible for Junction-LP and let $\rho \ge 128 \log_2(2k)$ be an integer.
--
--   **Lemma 2.5.** For every run of Algorithm 1 from the auxiliary graph, the number of pairs of $D'$ in no returned group is at most
--   $$\frac{|D'|}{2}.$$
--
--   Differences from the source:
--   - generalization: the algorithm's run with one implementation → every run of Algorithm 1; reason: the page leaves the choices open
--   - reading: ρ ≥ 128 log(2k), base not printed → 128 log₂(2k) ≤ ρ; reason: Lemma 2.5's last line needs base 2: 64 log₂ k/(128 ln k) > 1/2
--   - encoding: pairs discarded by Algorithm 1 → pairs of D′ whose vertex is in no returned group; reason: a pair vertex that is never discarded ends in a group, as its component has a pair vertex
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.5, p.14

import Mathlib
import Definitions.Def_MCPoise_JunctionLPFeasible
import Definitions.Def_MCPoise_auxGraph
import Definitions.Def_MCPoise_AssignRun

namespace MCPoise

open scoped Classical in
/-- **Lemma 2.5.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.5, p.14: "At most |D′|/2 pairs are discarded by Algorithm 1."

For every run of Algorithm 1 from the auxiliary graph of a feasible solution of Junction-LP: the demand indices of `D′` in no returned group number at
most `|D′|/2`.

**Formalization Note.** A pair is discarded exactly when its vertex is in no returned group: every pair vertex that is never discarded lies in a component
with a pair vertex, and that component ends in a group or recurses. -/
theorem lemma_2_5 (I : Inst) (L : ℕ) (x : Sym2 (Fin I.n) → ℝ) (x' : Sym2 (Fin I.n) → Fin I.k → ℝ)
    (lam : Fin I.k → Fin I.k → ℝ) (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ) (ρ : ℕ)
    (hLP : JunctionLPFeasible I L x x' lam f)
    (hρ : 128 * Real.logb 2 (2 * (I.k : ℝ)) ≤ (ρ : ℝ))
    (𝒞 : Set (AGroup (auxGraph lam))) (hrun : AssignRun ρ (auxInit lam) 𝒞) :
    2 * ((Dprime lam).filter fun i => ∀ G ∈ 𝒞, i ∉ pairsOf G.C).card ≤ (Dprime lam).card := by sorry

end MCPoise
