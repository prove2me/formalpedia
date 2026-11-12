-- Prove2me | Theorems.Thm_HDXConc_claim_3_1
-- name    : HDXConc.claim_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:00:11.263275+00:00
-- url     : https://prove2.me/theorems/863a656d-4f15-460e-a7aa-db68679283d2
-- title:
--   Claim 3.1, p.15 — $\mathrm{Var}_{\pi_{d,t}}(F)=d\,\mathrm{Var}_{\pi_{1,t}}(f)+d(d-1)\langle h,A_th\rangle_{\pi_{1,t}}$
-- statement:
--   Let $X$ be a pure $d$-dimensional complex, $d\ge2$, with top density $\pi_d$, let $f$ be a real function on the vertices, $t\in\mathbb R$, and $F(\sigma)=\sum_{v\in\sigma}f(v)$. With $h=f-\mathbb E_{\pi_{1,t}}f$,
--
--   $$\mathrm{Var}_{\pi_{d,t}}(F)=d\,\mathrm{Var}_{\pi_{1,t}}(f)+d(d-1)\,\langle h,A_th\rangle_{\pi_{1,t}}.$$
--
--   Here $\pi_{1,t},\pi_{2,t}$ are induced by the tilted density $\pi_{d,t}$, and $A_t$ is the walk operator of the underlying graph for $\pi_{2,t}$.
--
--   The identity relates the variance of a sum over a top face to the variance on vertices and the quadratic form of the walk, which is where spectral information enters.
--
--   Differences from the source:
--   - generalization: f : X(1) → [0, 1], the standing f of the proof → every f : V → ℝ; reason: the identity does not use the range of f, and the printed case is an instance
--   - encoding: a d-dimensional (pure) complex, with co-dimension 2 links and d − 1 in denominators → 2 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: this is the domain the statement is written for; dimension is the number of vertices, as in the paper, and the top density rules out the empty collection
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Claim 3.1, p.15 (proof p.31)

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_tilt
import Definitions.Def_HDXConc_topVar
import Definitions.Def_HDXConc_walkOp

namespace HDXConc

/-- Claim 3.1, p.15 (proof p.31):
`Var_{π_{d,t}}(F) = d Var_{π_{1,t}}(f) + d (d - 1) ⟨h, A_t h⟩_{π_{1,t}}`, where `h = f - E_{π_{1,t}} f`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** The identity holds for every `t ∈ ℝ` and every real `f`; the range `[0, 1]` of `f` is not
used. Since `tilt X d ρ f 0 = ρ` on `X(d)` for a density `ρ`, the case `t = 0` is the identity for an arbitrary
positive top density. `A_t` and the inner product are the printed ones of p.11 for `π_{1,t}`, `π_{2,t}`. -/
theorem claim_3_1 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d)
    {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π)
    (f : V → ℝ) (t : ℝ) :
    topVar X d (tilt X d π f t) (topSum f) =
      (d : ℝ) * vertexVar X d (tilt X d π f t) f +
        (d : ℝ) * ((d : ℝ) - 1) *
          vertexInner X d (tilt X d π f t)
            (fun v => f v - vertexMean X d (tilt X d π f t) f)
            (walkOp X d (tilt X d π f t) (fun v => f v - vertexMean X d (tilt X d π f t) f)) := by sorry

end HDXConc
