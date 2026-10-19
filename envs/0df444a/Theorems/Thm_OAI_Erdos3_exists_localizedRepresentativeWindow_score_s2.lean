-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_localizedRepresentativeWindow_score_s2
-- name    : OAI.Erdos3.exists_localizedRepresentativeWindow_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:42.137397+00:00
-- url     : https://prove2.me/theorems/b785d5e4-422a-4ad4-9b39-2d81a4dfcbe1
-- title:
--   A function with positive mean on Z/N keeps a proportional share of its mean on one localized representative window
-- statement:
--   Let $N$ be a nonzero natural number and $f : \mathbb{Z}/N \to \mathbb{R}$. Let $M, \sigma$ be real numbers with $M > 0$, $\sigma > 0$, $|f(x)| \le M$ for all $x$, and $\sigma \le \mathbb{E}_{x \in \mathbb{Z}/N} f(x)$ (uniform average). Let $\eta \in \mathbb{R}_{\ge 0}$ with $\eta > 0$, $\eta \le \sigma/(100M)$, and $1/N \le \sigma/(100M)$.
--
--   Then there is an index $i \in \mathrm{Fin}(\texttt{representativeWindowCount})$ such that
--   $$\frac{3\sigma}{4\cdot\texttt{representativeWindowCount}} \le \mathbb{E}_{x \in \mathbb{Z}/N}\ f(x)\cdot \texttt{(localizedRepresentativeWindow η heta i).value}\bigl(\mathrm{val}(x)/N\bigr),$$
--   where $\mathrm{val}(x) \in [0, N)$ is the standard representative of $x$, `representativeWindowCount` is a fixed positive natural number defined by OpenAI (the number of sites of a fixed partition of the unit interval at scale $1/16$), and `localizedRepresentativeWindow η heta i` is the `RepresentativeWindow` defined by OpenAI whose value at $t$ is the product of an interior cutoff at scale $\eta$ with the $i$-th weight of that partition of unity (a $[0,1]$-valued Lipschitz function supported in $(0, 1)$).
--
--   Lean: `OAI.Erdos3.exists_localizedRepresentativeWindow_score_s2`, which states OpenAI's `OAI.Erdos3.exists_localizedRepresentativeWindow_score` (in `lean/OAI/Combinatorics/Progressions/Estimates/RepresentativeWindowPatch.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RepresentativeWindowPatch.lean (declaration OAI.Erdos3.exists_localizedRepresentativeWindow_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_localizedRepresentativeWindow_score_s2 {N : ℕ} [NeZero N]
    (f : ZMod N → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    ∃ i : Fin representativeWindowCount, 3 * sigma / (4 * representativeWindowCount) ≤
      𝔼 x, f x * (localizedRepresentativeWindow eta heta i).value ((x.val : ℝ) / N) := by
  sorry

end Erdos3

end

end OAI
end
