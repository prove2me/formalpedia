-- Prove2me | Theorems.Thm_GnpColoring_theorem_3_3
-- name    : GnpColoring.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:19.546723+00:00
-- url     : https://prove2.me/theorems/d8cb4ddb-fb09-4f3b-b744-bb693a4f0ce2
-- title:
--   Theorem 3.3 — block dynamics gap $\Omega_{\varepsilon,\eta}(d^{\varepsilon-1/2})$
-- statement:
--   Fix $0\le\varepsilon\le1/2$ and $0<\eta<\varepsilon$. There is $c>0$, depending only on $\varepsilon,\eta$, and thresholds $A_0,C_0$ such that for all $A\ge A_0$, $C\ge C_0$ and sufficiently large $d$, with probability $1-o(1)$ as $n\to\infty$ over $G\sim G(n,d/n)$: for every integer $q\ge d+d^{1/2+\varepsilon}$ and every valid block partition of $G$, the block generator $L$ for the uniform measure on proper $q$-colourings satisfies
--
--   $$\mathrm{gap}(L)\ge c\,d^{\varepsilon-1/2}.$$
--
--   This is the spectral gap of the block dynamics that Section 5 compares with Glauber dynamics.
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
--   - encoding: $\mathrm{gap}(L)=\Omega_{\varepsilon,\eta}(d^{\varepsilon-1/2})$ → $\exists c>0$ before $A,C,d$; Poincaré inequality with constant $c\,d^{\varepsilon-1/2}$; reason: meaning of $\Omega_{\varepsilon,\eta}$; gap as Poincaré inequality (p.14)
--   - reading: "for sufficiently large A, C, d" → independent thresholds $A_0$, $C_0$, then $d_0$; reason: the stronger of the two orderings
--   - reading: "every partition … whenever q ≥ d + d^{1/2+ε}" → $q$ and the partition quantified inside the event; reason: the stronger reading; the events used do not depend on $q$
--   - generalization: valid partitions for the diameter constant $D=D(\eta,A,C)$ fixed in Definition 3.2 before $d$ → every $D>0$, quantified inside the event, after $d_0$, so the bound is uniform in $D$; reason: the proof (pp.34–35) uses Lemmas 3.18, 3.23, 3.27, 5.9 and Corollary 3.26, none of which uses the diameter condition; taking $D=D(\eta,A,C)$ gives the source's statement
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Theorem 3.3, p.16

import Mathlib
import Definitions.Def_GnpColoring_blockGen
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Theorem 3.3 (spectral gap for colouring block dynamics).** Fix `0 ≤ ε ≤ 1/2` and `0 < η < ε`.
There is `c > 0` (depending only on `ε, η`) such that for all sufficiently large `A, C, d`, with
probability `1 − o(1)` over `G ∼ G(n, d/n)`: for every integer `q ≥ d + d^(1/2+ε)` and every valid
block partition `S`, the block generator `L` satisfies `gap(L) ≥ c d^(ε − 1/2)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Theorem 3.3, p.16: "Fix any 0 ≤ ε ≤ 1/2 and 0 < η < ε. Then for sufficiently large A, C, d
and with high probability as n → ∞ over G ∼ G(n, d/n), every partition satisfying the block
assumptions from Definition 3.2 results in gap(L) = Ω_{ε,η}(d^(ε−1/2)) whenever the number of
colors q satisfies q ≥ d + d^(1/2+ε)."

**Formalization Note** `Ω_{ε,η}` is a constant `c > 0` chosen before `A, C, d`. "Sufficiently large
`A, C`" is read as independent thresholds `A₀, C₀`. `q` and the partition are quantified inside
the event ("whenever"; the event of Lemma 3.27 does not involve `q`). `gap(L) ≥ γ` is the
Poincaré inequality (`SpinGirth5.PoincareIneq`) for the uniform law on proper `q`-colourings. -/
theorem theorem_3_3 :
    ∀ ε η : ℝ, 0 ≤ ε → ε ≤ 1 / 2 → 0 < η → η < ε →
    ∃ c : ℝ, 0 < c ∧ ∃ A₀ C₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∀ C : ℝ, C₀ ≤ C →
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          ∀ q : ℕ, d + d ^ ((1 : ℝ) / 2 + ε) ≤ (q : ℝ) →
            ∀ (D : ℝ) (S : Finset (Fin n)), IsValidPartition G d η A C D S →
              SpinGirth5.PoincareIneq (MarkovMixing.properColoringDist G q) (blockGen G q S) (c * d ^ (ε - 1 / 2))))
        atTop (𝓝 1) := by sorry

end GnpColoring
