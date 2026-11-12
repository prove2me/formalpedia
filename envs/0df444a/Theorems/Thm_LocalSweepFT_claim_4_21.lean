-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_21
-- name    : LocalSweepFT.claim_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:52.881891+00:00
-- url     : https://prove2.me/theorems/5cbbc7b9-d9dc-493d-b9ab-ab576232de4c
-- title:
--   Claim 4.21 — every codeword of the small code $C_v$ extends to a stabilizer in $\mathrm{Stab}_v$
-- statement:
--   Let $d'\ge2$ and $d\ge d'+1$, and let $v$ be a vertex of the infinite cover $\mathcal T^d_\infty$. For every $d'$-chain $z$ rooted at $v$ with $(\partial^-z)|_{v+}=0$ (the small code $C_v$) there is a $d'$-chain $w$ with $\partial^-w=0$, supported on the $d'$-cells rooted at $v$ and the cells $\theta_{gv,S'}$ with $g\notin S'$ (the stabilizer code $\mathrm{Stab}_v$), such that $w|_{v+}=z$: $z$ and $w$ agree on the faces rooted at $v$.
--
--   It shows that the corner of a reduced error sees a syndrome, which drives Claims 4.24 and 4.27.
--
--   Differences from the source:
--   - encoding: a vertex of the complex of §4.3 → a vertex of ℤ^d (the ∞-lift); reason: §4.3 works on the ∞-lift (p.24)
--   - reading: "z = w|_v; namely, z and w agree on the faces rooted at v" → w|_{v+} = z; reason: the explanation after "namely"; z is rooted at v
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.21 with Definitions 4.19–4.20, pp.25–26

import Mathlib
import Definitions.Def_LocalSweepFT_Chain

namespace LocalSweepFT

/-- Claim 4.21, p.26, with Definitions 4.19–4.20, pp.25–26 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `v` be a vertex of the infinite cubical complex `T^d_∞`, `d′ ≥ 2`, `d ≥ d′ + 1`. For every `z` in the
small code `C_v` (a `d′`-chain rooted at `v` with `(∂⁻z)|_{v+} = 0`) there is a stabilizer `w` in
`Stab_v` (a `d′`-cycle, `∂⁻w = 0`, supported on the `d′`-cells rooted at `v` and the cells `θ_{gv,S′}`
with `g ∉ S′`) such that `w|_{v+} = z`: `z` and `w` agree on the faces rooted at `v`.

**Formalization Note.** Stated on the infinite cover `ℤ^d`, where §4.3 works ("we assume dealing
with the ∞-lift", p.24). -/
theorem claim_4_21 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : d' + 1 ≤ d) (v : Vtx ℤ d) (z : Chain ℤ d d')
    (hz : IsRootedAt v z) (hzc : restrictPos v (bdry z) = 0) :
    ∃ w : Chain ℤ d d', bdry w = 0 ∧
      (∀ c ∈ w.support, c.1 = v ∨ ∃ g : Fin d, g ∉ c.2.1 ∧ c.1 = v + unitVec g) ∧
      restrictPos v w = z := by sorry

end LocalSweepFT
