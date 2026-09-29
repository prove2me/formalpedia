-- Prove2me | Theorems.Thm_KServer_workFnU_quasiconvex
-- name    : KServer.workFnU_quasiconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:47:54.888738+00:00
-- url     : https://prove2.me/theorems/35f47a7a-5627-48b5-aec5-034c701bff99
-- title:
--   Quasiconvexity of the unordered work function
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$ and a request sequence $\sigma$; write $\widehat w$ for the unordered work function.
--
--   **Statement (quasiconvexity).** For all configurations $X$ and $Y$ there is a bijection $h:X\to Y$ such that for **every** splitting of $X$ into $X_1$ and $X_2$,
--   $$\widehat w(X)+\widehat w(Y)\;\ge\;\widehat w\bigl(X_1\cup h(X_2)\bigr)+\widehat w\bigl(h(X_1)\cup X_2\bigr).$$
--   The bijection is chosen once and works for all $2^k$ splittings simultaneously; that uniformity is the whole strength of the property.
--
--   **Role.** Quasiconvexity is what distinguishes work functions from arbitrary functions satisfying the obvious properties — nonnegativity, the Lipschitz bound, monotonicity in the request sequence. It is not used directly in the analysis of the Work Function Algorithm; it is used to establish the *duality property*, and duality is what the proof of the $(2k-1)$ bound rests on. It is therefore the single lemma standing between the machinery already proved here and the two remaining general upper bounds, `KServer.workFnU_growth_two_server_inj` and `KServer.workFnU_growth_2k_inj`.
--
--   **Proof sketch.** Normalise both optimal solutions to be lazy (`KServer.lazy_schedule`), so each is $k$ directed paths that start at $C_0$, pass through the requests in order, and end at $X$ (colour them blue) or at $Y$ (red). Every request is an interior node of exactly one blue and one red path, so it has in-degree and out-degree $1$ in each colour; the points of $C_0$ have out-degree $1$ in each colour, those of $X$ blue in-degree $1$, those of $Y$ red in-degree $1$.
--
--   Given $x\in X$, walk backwards along the blue edge entering $x$, then forwards along the red edge leaving the node reached, then backwards along blue again, and so on, recolouring each edge as it is traversed. The walk cannot branch or repeat and must end at a point of $Y$; setting $h(x)$ to that endpoint defines a bijection. Running the walk from every point of $X_2$ turns the blue edges into $k$ paths ending at $X_1\cup h(X_2)$ and the red ones into $k$ paths ending at $h(X_1)\cup X_2$, and these are feasible — not necessarily optimal — solutions for the two right-hand work functions. No edge changed length, only colour, so the total is preserved and the inequality follows.
--
--   **Formalization Note** The splitting is indexed by a `Finset (Fin k)`: `s` plays the role of $X_1$, and the bijection $h$ is the permutation `π`, so $X_1\cup h(X_2)$ is `fun i => if i ∈ s then X i else Y (π i)`. This transcription is faithful only for the *unordered* work function `workFnU`: for the labelled `workFn` it would pin down a labelling that the classical statement leaves free, and the classical inequality would not imply it. The survey notes that the argument does not use the triangle inequality, so it is valid for arbitrary distance functions.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, Definition 2 (Quasiconvexity) and the graphical proof following it, with Figure 2; an algebraic derivation is in E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_quasiconvex (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    ∃ π : Equiv.Perm (Fin k), ∀ s : Finset (Fin k),
      workFnU C₀ σ (fun i => if i ∈ s then X i else Y (π i))
        + workFnU C₀ σ (fun i => if i ∈ s then Y (π i) else X i)
        ≤ workFnU C₀ σ X + workFnU C₀ σ Y := by sorry

end KServer
