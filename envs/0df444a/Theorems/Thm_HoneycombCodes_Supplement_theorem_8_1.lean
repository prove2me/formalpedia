-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_8_1
-- name    : HoneycombCodes.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:38:49.398345+00:00
-- url     : https://prove2.me/theorems/6a818b23-807e-46e2-99d5-7c4b0870bb9f
-- title:
--   Theorem 8.1 — higher-row bounds $A_2(n,d)\le\mathrm{HC}^{row}_{r+1}(n,d)\le\mathrm{HC}^{row}_r(n,d)$, level one is Theorem 4.8, exponent $\kappa_{HC}$
-- statement:
--   For every $n\ge1$ and $d$:
--
--   1. for every $r\ge1$,
--   $$
--   A_2(n,d)\le\mathrm{HC}^{row}_{r+1}(n,d)\le\mathrm{HC}^{row}_r(n,d);
--   $$
--   2. $\mathrm{HC}^{row}_1(n,d)$ is exactly the full finite profile optimization furnished by Theorem 4.8: the infimum, over $0\le k\le n/2$, connected finite sets $\Omega$ of valid triples and positive profiles $w$ with $\lambda_\Omega(w)>s_{n,d}=1-2d/n$, of
--   $$
--   \frac{1-s_{n,d}}{d_k(\lambda_\Omega(w)-s_{n,d})}\,D_\Omega(w),
--   $$
--   an empty infimum being $2^n$;
--   3. its explicit Følner-box, dimension-sum exponent is the first honeycomb exponent: for every $0<\delta<1/2$,
--   $$
--   \limsup_{n\to\infty}\frac1n\log_2\mathrm{HC}^{row}_1(n,\lceil\delta n\rceil)\le\kappa_{HC}(\delta).
--   $$
--
--   Here $A_2(n,d)$ is the largest size of a binary code of length $n$ and minimum distance $d$, and $\mathrm{HC}^{row}_r$ is the infimum of $B(h;s_{n,d})$ over the nested certificate library $\mathfrak C_r(n)$. Adding rows, and with them Littlewood–Richardson multiplicities, can only improve the finite bound.
--
--   Differences from the source:
--
--   - encoding: "for every $n,d$" → $n\ge1$; reason: $s_{n,d}=1-2d/n$ and $\ell_x=x/\sqrt n$ are undefined at $n=0$
--   - reading: "Its explicit Følner-box, dimension-sum exponent is the first honeycomb exponent $\kappa_{HC}$" → $\limsup_n\frac1n\log_2\mathrm{HC}^{row}_1(n,\lceil\delta n\rceil)\le\kappa_{HC}(\delta)$ for $0<\delta<1/2$; reason: the sentence names no separately defined object, the proof cites Theorem 5.5 (whose Følner-box certificates lie in $\mathfrak C_1(n)$), and the paper restates the clause in Theorem 1.4(b) as "$\mathrm{HC}_{1,0}(n,d)$ … whose exponent is at most $\kappa_{HC}$"
--   - encoding: $A_2$, $\kappa_{HC}$, $p_{\omega,\omega'}$, $D_\omega$, $d_k$, $\lambda_\Omega$, $D_\Omega$ → the published `PrettyGoodCriterion.A2`, `HoneycombCodes.kappaHC`, `pDir`, `Domega`, `dk`, `lamProfile`, `effDim`; reason: the same objects
--   - encoding: $\limsup_n$ (extended-real) → Lean's real `Filter.limsup` together with `Filter.IsBoundedUnder (· ≤ ·) atTop` of the same sequence; reason: the real `limsup` of a sequence unbounded above is the junk value $0$, and the bound $\limsup\le\kappa_{HC}(\delta)<\infty$ asserts boundedness above, so the pair says exactly the printed inequality
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §8, Theorem 8.1, p.41 (PDF 43); libraries and HC^row_r, p.40 (PDF 42); Theorem 1.4(b), p.6 (PDF 8)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_Supplement_HCrow

set_option autoImplicit false

namespace HoneycombCodes.Supplement

open Classical in
/-- **Theorem 8.1 (higher-row representation bounds)**, Gay, Granha Jeronimo, Liu, *The Honeycomb
Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.41 (PDF 43). For every
`n, d` and `r ≥ 1`:
(i) `A₂(n, d) ≤ HC^row_{r+1}(n, d) ≤ HC^row_r(n, d)`;
(ii) `HC^row_1(n, d)` is exactly the full finite profile optimization furnished by Theorem 4.8: the
infimum, over `0 ≤ k ≤ n/2`, connected finite sets `Ω` of valid triples and positive profiles `w`
with `λ_Ω(w) > s_{n,d}`, of `(1 − s_{n,d}) D_Ω(w)/(d_k(λ_Ω(w) − s_{n,d}))` (an empty infimum being
`2ⁿ`);
(iii) its explicit Følner-box, dimension-sum exponent is the first honeycomb exponent: for every
`0 < δ < 1/2`, `lim sup_{n→∞} (1/n) log₂ HC^row_1(n, ⌈δn⌉) ≤ κ_HC(δ)`.

**Formalization Note.** `A₂` and `κ_HC` are the published `PrettyGoodCriterion.A2`,
`HoneycombCodes.kappaHC`; `p_{ω,ω′}`, `D_ω`, `d_k`, `λ_Ω(w)`, `D_Ω(w)` are the published `pDir`,
`Domega`, `dk`, `lamProfile`, `effDim`. `n ≥ 1` (the threshold `s_{n,d} = 1 − 2d/n` and
`ℓ_x = x/√n` need it). Clause (iii) is read as an upper bound on the exponent of `HC^row_1`, as
Theorem 1.4(b) restates it ("whose exponent is at most κ_HC"). The real `limsup` is paired with
`IsBoundedUnder (· ≤ ·)`, so an unbounded sequence (whose real `limsup` is the junk value `0`) cannot
satisfy (iii); together they say the extended-real limsup is at most `κ_HC(δ)`. -/
theorem theorem_8_1 :
    (∀ (n d r : ℕ), 1 ≤ n → 1 ≤ r →
      (PrettyGoodCriterion.A2 n d : ℝ) ≤ HCrow (r + 1) n d ∧ HCrow (r + 1) n d ≤ HCrow r n d) ∧
    (∀ (n d : ℕ), 1 ≤ n →
      HCrow 1 n d =
        (if {B : ℝ | ∃ (k : ℕ) (Ω : Finset (ℕ × ℕ × ℕ)) (w : Ω → ℝ), 2 * k ≤ n ∧
              (∀ ω ∈ Ω, HoneycombCodes.IsValidTriple n k ω) ∧
              HoneycombCodes.IsConnectedOmega n k Ω ∧ (∀ ω, 0 < w ω) ∧
              sND n d < HoneycombCodes.lamProfile (fun a b : Ω => HoneycombCodes.pDir n k a b) w ∧
              B = (1 - sND n d) /
                  (HoneycombCodes.dk n k *
                    (HoneycombCodes.lamProfile (fun a b : Ω => HoneycombCodes.pDir n k a b) w -
                      sND n d)) *
                HoneycombCodes.effDim (fun ω : Ω => HoneycombCodes.Domega n ω) w} = ∅
          then (2 : ℝ) ^ n
          else sInf {B : ℝ | ∃ (k : ℕ) (Ω : Finset (ℕ × ℕ × ℕ)) (w : Ω → ℝ), 2 * k ≤ n ∧
              (∀ ω ∈ Ω, HoneycombCodes.IsValidTriple n k ω) ∧
              HoneycombCodes.IsConnectedOmega n k Ω ∧ (∀ ω, 0 < w ω) ∧
              sND n d < HoneycombCodes.lamProfile (fun a b : Ω => HoneycombCodes.pDir n k a b) w ∧
              B = (1 - sND n d) /
                  (HoneycombCodes.dk n k *
                    (HoneycombCodes.lamProfile (fun a b : Ω => HoneycombCodes.pDir n k a b) w -
                      sND n d)) *
                HoneycombCodes.effDim (fun ω : Ω => HoneycombCodes.Domega n ω) w})) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n : ℕ => Real.logb 2 (HCrow 1 n ⌈δ * n⌉₊) / n) ∧
        Filter.limsup (fun n : ℕ => Real.logb 2 (HCrow 1 n ⌈δ * n⌉₊) / n) Filter.atTop ≤
          HoneycombCodes.kappaHC δ) := by sorry

end HoneycombCodes.Supplement
