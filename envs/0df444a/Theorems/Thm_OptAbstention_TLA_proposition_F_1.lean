-- Prove2me | Theorems.Thm_OptAbstention_TLA_proposition_F_1
-- name    : OptAbstention.TLA.proposition_F_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:08:10.719526+00:00
-- url     : https://prove2.me/theorems/58616375-633e-4523-8b80-84e31f8bf765
-- title:
--   Proposition F.1: $S$ is an $(S_{\mathrm{cln}},\theta)$-corruption iff $d_{\mathrm{TV}}(U(S),U(S_{\mathrm{cln}}))\le\theta$
-- statement:
--   Let $S_{\mathrm{cln}},S$ be nonempty finite multisets of equal cardinality $n$ and $\theta\in[0,1]$. Then $S$ is an $(S_{\mathrm{cln}},\theta)$-corruption if and only if
--   $$d_{\mathrm{TV}}(U(S),U(S_{\mathrm{cln}}))\le\theta .$$
--   It converts the adversary's replacements into the empirical total variation distance of the abstention benchmark.
--
--   Differences from the source:
--   - encoding: nonempty finite multisets of equal cardinality → lists Fin n → Ω, n ≥ 1, over any type Ω, compared through their multisets; reason: the statement depends only on the multisets
--   - encoding: d_TV(U(S), U(S_cln)) → ½∑_v |m_S(v)/n − m_{S_cln}(v)/n|; reason: the total variation distance of two finitely supported distributions
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 49, Proposition F.1

import Mathlib
import Definitions.Def_OptAbstention_TLA_Empirical

namespace OptAbstention.TLA

/-- Proposition F.1, p. 49: for nonempty multisets `S_cln, S` of equal cardinality and
`θ ∈ [0, 1]`, `S` is an `(S_cln, θ)`-corruption iff `d_TV(U(S), U(S_cln)) ≤ θ`. -/
theorem proposition_F_1 {Ω : Type*} (n : ℕ) (hn : 1 ≤ n) (Scln S : Fin n → Ω) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsCorruption Scln S θ ↔ empTV S Scln ≤ θ := by sorry

end OptAbstention.TLA
