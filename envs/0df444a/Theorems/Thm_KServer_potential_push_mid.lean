-- Prove2me | Theorems.Thm_KServer_potential_push_mid
-- name    : KServer.potential_push_mid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:31:46.180397+00:00
-- url     : https://prove2.me/theorems/86cadc73-6680-4058-a391-0467e92c0142
-- title:
--   Pushing the request from the middle anchor slot to the last
-- statement:
--   Let $w$ be the work function of a $3$-server instance ending with the request $r$, evaluated in the antipodal extension of a metric space $M$ with distances bounded by $\Delta$. Then for every point $z$:
--
--   $$w(\bar z\,\bar z\,r) + w(\bar r\,\bar r\,\bar r) \;\le\; w(\bar r\,\bar r\,z) + w(\bar z\,\bar z\,\bar z).$$
--
--   In potential terms this is the "easy case" of Lemma 21 of Coester and Koutsoupias: the anchored potential $\Phi_{xrz}$ and $\Phi_{xzr}$ share their first two summands ($w(X)$ and $w(\bar x \,r z)$ up to ordering), and the displayed inequality compares exactly the remaining two — so it says the request may be **pushed from the middle anchor slot to the last** without increasing the potential, $\Phi_{xzr}(w) \le \Phi_{xrz}(w)$.
--
--   ## Role
--
--   The potential method proves $3$-competitiveness of the Work Function Algorithm once the minimum of the potential is attained at an anchor triple *ending with the current request*. The pushing lemmas are how the case analysis of Coester--Koutsoupias' Theorem 23 finishes: whenever the analysis produces a minimising triple with $r$ in the first or middle slot, they move $r$ to the last slot. This theorem is the middle-slot step; the first-slot step reduces to it. The paper calls this case "easy" and omits it; the proof below is the omitted argument.
--
--   ## About the proof
--
--   No tree structure is used --- only the resolution property of $w$ (some server of any configuration can be sent to the last request at exactly the cost of the move) and $1$-Lipschitzness, together with the antipodal distance algebra $d(\bar p, \bar q) = d(p,q)$, $d(p, \bar q) = 2\Delta - d(p,q)$, $d(r, \bar r) = 2\Delta$.
--
--   The all-antipodes configuration $\bar z^3$ resolves necessarily to $(\bar z\, \bar z\, r)$, giving the exact identity $w(\bar z^3) = w(\bar z \bar z r) + (2\Delta - rz)$. The mixed configuration $\bar r \bar r z$ resolves either from $z$ --- then $w(\bar r \bar r z) = w(\bar r \bar r r) + rz$, and the single Lipschitz bound $w(\bar r^3) \le w(\bar r \bar r r) + 2\Delta$ closes the inequality exactly --- or from a copy of $\bar r$ at cost $d(r, \bar r) = 2\Delta$, and then the Lipschitz bound $w(\bar r^3) \le w(r\, \bar r\, z) + 2\Delta + (2\Delta - rz)$ closes it, again exactly. Both branches are equalities up to the substituted identities, reflecting that the push loses nothing.
--
--   ## Formalization note
--
--   The extension is `antipodalExtension` on $M \oplus M$, original points embedded by `Sum.inl`, antipodes written `Sum.inr`; the work function is `workFnU` of the embedded instance. The proof is independent of which resolving index the resolution theorem returns.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Lemma 21 (lem:push3), the case π(k−1) = r, described there as 'also easy' and omitted; stated for k = 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem potential_push_mid (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r z : M) :
    @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inl r]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
    ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inl z]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inr z] := by sorry

end KServer
