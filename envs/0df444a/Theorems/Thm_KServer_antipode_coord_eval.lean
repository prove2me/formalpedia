-- Prove2me | Theorems.Thm_KServer_antipode_coord_eval
-- name    : KServer.antipode_coord_eval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:54:11.746715+00:00
-- url     : https://prove2.me/theorems/8af03326-72c2-4883-813e-65bd15ae4e0c
-- title:
--   Antipodal coordinates evaluate through original points
-- statement:
--   In the antipodal extension of a bounded metric space, consider the work function $w$ of an instance whose initial configuration and requests are original points. The McShane envelope theorem expresses $w$ at any configuration through an original configuration matched in *all three* coordinates. This theorem gives the sharper, coordinate-local form used in practice: a configuration with one or two antipodal coordinates and the rest original evaluates by replacing **only the antipodal coordinates**, the original ones staying fixed:
--
--   $$w(\bar x, y, c) = \min_{u} \bigl( w(u, y, c) + 2\Delta - d(u,x) \bigr), \qquad w(\bar x, \bar y, c) = \min_{u,v} \bigl( w(u,v,c) + (2\Delta - d(u,x)) + (2\Delta - d(v,y)) \bigr),$$
--
--   both minima over original points and attained (the formal statement exhibits the minimisers; the $\le$ direction over arbitrary $u, v$ is $1$-Lipschitzness).
--
--   ## Why the collapse is legitimate
--
--   The envelope theorem provides an original triple $A$ matched to all three coordinates. For the coordinates that were already original, $1$-Lipschitzness of the original work function lets $A$'s corresponding entries walk back to them at exactly the matching cost they were charged --- so the minimum with those coordinates pinned is no larger, and the Lipschitz bound shows it is no smaller. In other words: the freedom to move original coordinates in the envelope buys nothing.
--
--   ## Role
--
--   The one-coordinate form identifies the $x_1$-dependent part of the Coester--Koutsoupias potential $\Phi_{x_1x_2x_3}(w) = w(x_1x_2x_3) + w(\bar x_1 x_2 x_3) + \cdots$ with the one-server potential of the restricted function $u \mapsto w(u\,x_2 x_3)$ --- the bridge through which the one-server anchor lemma (their Lemma 24) drives the choice of the first anchor. The two-coordinate form does the same for the third summand $w(\bar x_2 \bar x_2 x_3)$, whose minimisers the greedy exchange relocates; it is how the resolution of $\bar x_2 \bar x_2 x_3$ *to* a chosen point $x_1$ is established in their Lemma 25. Both are stated for an arbitrary request sequence --- no last-request structure is needed.
-- source:
--   Coordinate-local form of the McShane envelope of the extension work function, as used implicitly throughout the tree and multi-ray analyses of C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474 (Lemmas 24, 25 and the potential's term-by-term manipulations).

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem antipode_coord_eval (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (x y c : M) :
    (∃ u : M,
      @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x, Sum.inl y, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inl u, Sum.inl y, Sum.inl c]
          + (2 * Δ - dist u x))
    ∧ (∃ u v : M,
      @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x, Sum.inr y, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inl u, Sum.inl v, Sum.inl c]
          + ((2 * Δ - dist u x) + (2 * Δ - dist v y))) := by sorry

end KServer
