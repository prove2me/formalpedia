-- Prove2me | Theorems.Thm_IPEComm1531_Main_fact_2_3
-- name    : IPEComm1531.Main.fact_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:32.287704+00:00
-- url     : https://prove2.me/theorems/92560455-cced-488c-b691-e31c25a214de
-- title:
--   Fact 2.3 — explicit strong $(r/2,1/r)$-extractors with seed $O(\log r)$ (Guruswami–Umans–Vadhan)
-- statement:
--   There is a family of maps $\mathrm{Ext}:\{0,1\}^r\times\{0,1\}^d\to\{0,1\}^\ell$, a constant $C>0$ and a threshold $R$ such that for every integer $r\ge R$ and every integer $1\le\ell\le r/3$:
--
--   1. the seed length $d=d(r,\ell)$ is a positive integer with $d\le C\log_2 r$;
--   2. $\mathrm{Ext}$ is a strong $(r/2,1/r)$-extractor: for every source $u$ with $H_\infty(u)\ge r/2$ and an independent uniform seed $\sigma$, $\mathrm{TV}((\sigma,\mathrm{Ext}(u,\sigma)),(\sigma,c))\le 1/r$ for uniform independent $c$;
--   3. one deterministic machine evaluates $\mathrm{Ext}(u,\sigma)$ in time polynomial in $r$ on all these inputs.
--
--   This supplies the certificates $c_\sigma=\mathrm{Ext}(u,\sigma)\oplus\mathrm{Ext}(v,\sigma)$ of IPE and the extraction step in the rectangle bound.
--
--   Differences from the source:
--   - encoding: d = O(log r) → d ≤ C log₂ r with one C for all r ≥ R and all ℓ; reason: standard unpacking of O(·); the bound in the source does not depend on ℓ
--   - encoding: Definition 2.2 takes d to be a positive integer → 1 ≤ d; reason: the positivity is part of Definition 2.2
--   - encoding: explicit, deterministic evaluation in poly(r) time → one Mathlib multi-stack Turing machine with time polynomial in the input code (r, ℓ in unary, then u, σ); reason: the code length lies between r and a constant multiple of r, so the bound is poly(r)
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Fact 2.3, p.7

import Mathlib
import Definitions.Def_IPEComm1531_Main_Extractor

namespace IPEComm1531.Main

/-- Fact 2.3 (Guruswami–Umans–Vadhan), p.7. -/
theorem fact_2_3 :
    ∃ E : Extractors, ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, E.GoodFrom C R ∧ E.EffectiveFrom R := by sorry

end IPEComm1531.Main
