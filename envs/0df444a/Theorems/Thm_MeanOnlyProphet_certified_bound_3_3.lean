-- Prove2me | Theorems.Thm_MeanOnlyProphet_certified_bound_3_3
-- name    : MeanOnlyProphet.certified_bound_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:24:03.340206+00:00
-- url     : https://prove2.me/theorems/50466927-704c-4e76-bc42-a3e97b881091
-- title:
--   §3.3 certified bound — forty slopes with $L(b,q)\ge 0.74190517$ for every rate
-- statement:
--   There are forty slopes $0<b_1\le b_2\le\dots\le b_{40}$ such that the step drop rate $b$ with these slopes on the forty equal intervals of $[0,1]$, and its threshold $\theta(t)=\int_t^1 b$, satisfy
--   $$
--   \theta(0)=0.74196156\ldots\quad(\text{so }\theta(0)<0.741962),\qquad b_{40}<1.81532,
--   $$
--   and, for every real rate $q$ that is nonnegative and nondecreasing on $[0,1]$,
--   $$
--   L(b,q)\ \ge\ \gamma=0.74190517 .
--   $$
--   This is the numerical certificate of the paper (backward evaluation of a factor-revealing LP with $N_t=640$, $N_y=1200$, $N_q=131{,}093$). Together with the transfer to finite $n$ it gives the $0.7419$ guarantee of Theorem 1.1; the two bounds on $\theta(0)$ and $b_{40}$ give $\theta(0)+\frac9{64}b_{40}<0.997242<1$, which the transfer uses.
--
--   Differences from the source:
--   - reading: the forty drop rates obtained by the paper's heuristic search (given only in the certificate data, not printed) → ∃ bs : Fin 40 → ℝ with every printed property (positive, nondecreasing, θ(0) = 0.74196156…, b_40 < 1.81532, L ≥ 0.74190517 for all rates); reason: the source does not print the slopes, so the statement asserts the existence of slopes with all the printed properties, which is what Theorem 3.5's proof uses
--   - encoding: γ = 0.74190517 . . . → the exact decimal 0.74190517 as a lower bound; reason: the printed digits truncate γ, so γ ≥ 0.74190517
--   - encoding: θ(0) = 0.74196156 . . . → 0.74196156 ≤ θ(0) < 0.74196157; reason: the printed digits truncate θ(0); this implies the bound θ(0) < 0.741962 recalled on p.30
--   - encoding: every nonnegative nondecreasing rate q → every real q ≥ 0, MonotoneOn on [0,1], entering as toRate q; reason: rates of §3 are real (bounded on [0,1] by monotonicity)
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §3.3, p.11 (PDF p.12); bounds recalled in App. A.2, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Lfun

namespace MeanOnlyProphet

/-- **§3.3, the certified bound for the forty-slope drop rate.** Feng, Jin, Wu, Xiang, *Mean-only
Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §3.3, p.11 (PDF p.12): "We use N = 40 positive
nondecreasing drop rates obtained by this search. With Nt = 640, Ny = 1200, and Nq = 131,093, the
following lower bound can be verified … γ = 0.74190517 . . . , and θ(0) = 0.74196156 . . . ." and "for
every nonnegative nondecreasing rate q, we obtain L(b, q) ≥ θ(0) + V0 (1, 0) ≥ θ(0) + v0,Ny ,0 ≥ γ";
App. A.2, p.30 (PDF p.31): "the threshold determined in Section 3 satisfies θ(0) < 0.741962 and b40 <
1.81532".

There are forty positive nondecreasing slopes `b_1 ≤ ⋯ ≤ b_40` whose step drop rate `b` has
`θ(0) = ∫_0^1 b = 0.74196156…` (so `θ(0) < 0.741962`) and `b_40 < 1.81532`, and `L(b, q) ≥ 0.74190517` for every real rate `q` that
is nonnegative and nondecreasing on `[0,1]`.

**Formalization Note.** The paper fixes the slopes in its certificate data and does not print them;
the statement is existential in them. `bs : Fin 40 → ℝ` is 0-based (`bs 39` is `b_40`). The
certificate sizes `N_t, N_y, N_q` are proof data and are not part of the statement. The constants are
exact decimals in `ℝ`; `θ(0) = 0.74196156 . . .` is the truncation `0.74196156 ≤ θ(0) < 0.74196157`, which
implies the bound `θ(0) < 0.741962` recalled on p.30. -/
theorem certified_bound_3_3 :
    ∃ bs : Fin 40 → ℝ, (∀ i, 0 < bs i) ∧ Monotone bs ∧
      0.74196156 ≤ thetaOf (stepRate bs) 0 ∧ thetaOf (stepRate bs) 0 < 0.74196157 ∧
      bs 39 < 1.81532 ∧
      ∀ q : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q t) → MonotoneOn q (Set.Icc 0 1) →
        (0.74190517 : ℝ) ≤ Lfun (stepRate bs) (toRate q) := by sorry

end MeanOnlyProphet
