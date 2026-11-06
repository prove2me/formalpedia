-- Prove2me | Theorems.Thm_GradSuffice_ref4_theorem_50
-- name    : GradSuffice.ref4_theorem_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:10.577193+00:00
-- url     : https://prove2.me/theorems/f432fba5-df5f-4b9f-a9fe-5058a3fa5460
-- title:
--   [4, Theorem 50], p.37 — agnostic regret $C\sqrt{dm\log(em/d)}$ for partial concept classes
-- statement:
--   Let $H$ be a class of partial concepts $h:Z\to\{0,1,\star\}$; a partial concept errs on an example whenever its value is not the label, in particular whenever it is undefined.
--
--   **Theorem ([4, Theorem 50]), as quoted.** There is a universal constant $C>0$ such that for every nonempty partial concept class $H$ with finite Littlestone dimension $d\ge1$ and every integer $m\ge d$ there is a randomized online learner with
--   $$\mathbb E\Big[\sum_{t=1}^m\mathbb 1\{\hat y_t\neq y_t\}\Big]-\min_{h\in H}\sum_{t=1}^m\mathbb 1\{h(z_t)\neq y_t\}\ \le\ C\sqrt{d\,m\log(em/d)}\tag{32}$$
--   for every fixed sequence $(z_1,y_1),\dots,(z_m,y_m)$, the expectation being over the learner's randomness. At round $t$ the learner sees $z_t$ and the past labelled examples and predicts $\hat y_t\in\{0,1\}$.
--
--   The paper applies this regret bound (Alon, Hanneke, Holzman and Moran) to the partial class of loved directions of a tree, whose Littlestone trees are its fully loving subtrees, to prove Proposition 1.
--
--   Differences from the source:
--   - encoding: randomized online learner, E[number of mistakes] → per-round prediction probabilities P_t(history, z_t) ∈ [0, 1]; expected mistakes ∑_t |P_t − 𝟙{y_t = 1}|; reason: against a fixed sequence the expected mistakes of a randomized learner depend only on these probabilities, and every family of probabilities is a randomized learner
--   - encoding: partial concepts Z → {0, 1, ⋆}, finite Littlestone dimension d → Z → Option Bool; HasLdim H d (a Littlestone tree of depth d, none of depth d + 1); reason: same objects
--   - reading: log (no base printed) → natural logarithm; reason: the e inside log(em/d) indicates the natural logarithm
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), App. B.1, Theorem ([4, Theorem 50]), p.37, Eq. (32)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_HasLdim

namespace GradSuffice

/-- **[4, Theorem 50] (agnostic regret for partial concept classes), as quoted.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, App. B.1,
p.37: "Theorem ([4, Theorem 50]). There is a universal constant `C > 0` such that, for every nonempty
partial concept class `H` with finite Littlestone dimension `d ≥ 1` and every integer `m ≥ d`, there is
a randomized online learner satisfying `E[∑_{t=1}^m 𝟙{ŷ_t ≠ y_t}] − min_{h∈H} ∑_{t=1}^m 𝟙{h(z_t) ≠ y_t}
≤ C √(d m log(em/d))` (32) for every fixed sequence `(z₁, y₁), …, (z_m, y_m)`. The expectation is over
the learner's randomness." Same page: "a mistake incurs loss one; for a partial concept, an
undefined prediction also incurs loss one against either label."

**Formalization Note.** Partial concepts are `Z → Option Bool` (`none` = `⋆`); labels `0, 1` are
`false, true`. A randomized learner is described, round by round, by the probability `P t h z ∈ [0,1]`
of predicting `1` on the example `z` after the labelled history `h`; against a fixed sequence its
expected number of mistakes is `∑_t |P_t − 𝟙{y_t = 1}|`, and every randomized learner induces such
probabilities (and conversely). `min_{h∈H}` is `sInf` of the finite nonempty set of counts. `log` is
natural. -/
theorem ref4_theorem_50 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type) (H : Set (Z → Option Bool)), H.Nonempty →
      ∀ d : ℕ, 1 ≤ d → HasLdim H d → ∀ m : ℕ, d ≤ m →
      ∃ P : (t : Fin m) → (Fin t → Z × Bool) → Z → ℝ,
        (∀ t h z, 0 ≤ P t h z ∧ P t h z ≤ 1) ∧
        ∀ (zs : Fin m → Z) (ys : Fin m → Bool),
          (∑ t : Fin m, |P t (NondualOpt.histPrefix (fun s => (zs s, ys s)) t) (zs t) -
              (if ys t then 1 else 0)|) -
            sInf ((fun h : Z → Option Bool =>
              ∑ t : Fin m, (if h (zs t) = some (ys t) then (0 : ℝ) else 1)) '' H) ≤
          C * √((d : ℝ) * m * Real.log (Real.exp 1 * m / d)) := by sorry

end GradSuffice
