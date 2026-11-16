-- Prove2me | Theorems.Thm_IntervalExplore_KT1_Supplement_lemma_11
-- name    : IntervalExplore.KT1.Supplement.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:00:34.774603+00:00
-- url     : https://prove2.me/theorems/a5e09398-447d-40a2-9adc-cf9e75d78b3e
-- title:
--   Lemma 11 — monotonicity of $m\ln n/(1+\ln m-\ln n)$
-- statement:
--   Let
--   $$
--   f(m,n)=\frac{m\ln n}{1+\ln m-\ln n}
--   $$
--   for real $m,n$ with natural logarithms. Then $f$ is strictly increasing in each argument on the region $n\ge3$, $m\ge n$:
--
--   1. for every real $n\ge3$, the map $m\mapsto f(m,n)$ is strictly increasing on $[n,\infty)$;
--   2. for every real $m$, the map $n\mapsto f(m,n)$ is strictly increasing on $[3,m]$.
--
--   Since $f(m,n)=\xi(n,m)\,m$, this gives the monotonicity of the window $\tau(n,m)$ in both parameters, used for the running estimates $(n',m')$ of the KT0 algorithm (footnote 6, p.11).
--
--   Differences from the source:
--   - reading: "monotonically increasing in both m and n for all n ≥ 3 and m ≥ n" → strictly increasing in m on [n, ∞) for each n ≥ 3 and strictly increasing in n on [3, m] for each m; reason: the phrase is ambiguous between nondecreasing and strictly increasing, and the stronger reading is taken; it implies the nondecreasing form used in footnote 6
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Appendix A, Lemma 11, p.18 (PDF p.19)

import Definitions.Def_IntervalExplore_KT1_Supplement_Model

set_option autoImplicit false

namespace IntervalExplore.KT1.Supplement

/-- Lemma 11, p.18 (PDF p.19). Read as strict monotonicity (the stronger reading of
"monotonically increasing"): in m on [n, ∞) for every real n ≥ 3, and in n on [3, m]
for every real m. -/
theorem lemma_11 :
    (∀ n : ℝ, 3 ≤ n → StrictMonoOn (fun m : ℝ => lemma11F m n) (Set.Ici n)) ∧
    (∀ m : ℝ, StrictMonoOn (fun n : ℝ => lemma11F m n) (Set.Icc 3 m)) := by sorry

end IntervalExplore.KT1.Supplement
