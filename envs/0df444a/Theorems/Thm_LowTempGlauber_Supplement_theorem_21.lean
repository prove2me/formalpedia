-- Prove2me | Theorems.Thm_LowTempGlauber_Supplement_theorem_21
-- name    : LowTempGlauber.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:30:23.345193+00:00
-- url     : https://prove2.me/theorems/6900715a-46ae-4d57-a85e-363b65b6a25e
-- title:
--   Theorem 21 — whp, independent lifted random-cluster samples have small inactive excess, small disagreement components and typical edge counts, except with probability $n^{-D}$
-- statement:
--   Let $d\ge3$ be an integer and $q>2$ a real, $\beta_c=\beta_c(q,d)$, and let $\hat\pi^\pm$ be the lifted random-cluster laws on compatible pairs $\omega=(F,S)$, with the events $A_{G,R}$ (an inactive graph has total tree excess $>R$), $B_{G,\ell,r}$ (the disagreement graph $H(\omega,\omega')$ has a component with more than $\ell$ vertices or tree excess more than $r$) and $H^\pm_\theta$ (an edge count on the wrong side of $n(p_c\pm3\theta)$).
--
--   There is a constant $\theta>0$ and a $\delta_0>0$ such that for every $\delta\in(0,\delta_0)$ and every $D>0$ there are constants $C,C'>0$ and an integer $r\ge1$ with the following property. With probability $1-o(1)$ over a uniformly random $d$-regular graph $G$ on $n$ vertices, setting $R=C\frac{\log n}{\log\log n}$ and $\ell=\lceil C'\log n\rceil$:
--   1. for every $\beta>0$ with $\beta>\beta_c-\delta$ and every choice of the largest component in $\hat\pi^+$,
--   $$\Pr_{\omega,\omega'\sim\hat\pi^+}\bigl[(\omega,\omega')\in A_{G,R}\cup B_{G,\ell,r}\cup H^+_\theta\bigr]\le n^{-D};$$
--   2. for every $0<\beta<\beta_c+\delta$,
--   $$\Pr_{\omega,\omega'\sim\hat\pi^-}\bigl[(\omega,\omega')\in A_{G,R}\cup B_{G,\ell,r}\cup H^-_\theta\bigr]\le n^{-D},$$
--   with $\omega,\omega'$ independent.
--
--   This is the random-graph estimate behind Theorem 2: it supplies the bad-event probability in the weak-Poincaré inequality for the random-cluster phases (Lemma 22), and the bound is uniform in $\beta$ on each range.
--
--   **Formalization Note** The probability is the double sum of $\hat\pi^\pm(\omega)\hat\pi^\pm(\omega')$ over pairs in the event. "With probability $1-o(1)$" is the published `WithHighProb d`; $\beta$ and the choice of largest component are quantified inside that event.
--
--   Differences from the source:
--   - reading: "For some small constant θ > 0, define also H^±_θ" (p.23, before the theorem) → ∃ θ > 0, quantified before δ and D; reason: θ is a fixed constant of the definitions; the proof (p.43) takes it from Lemma 40 together with δ
--   - reading: "for any sufficiently small δ > 0" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the standard meaning of "sufficiently small"
--   - reading: "the largest component C₁(ω)" in the definition of π̂⁺ (p.22) → every choice c of a component of (V, F) of maximum size, quantified inside the whp event; reason: the paper fixes no tie-break; π̂⁺ is a probability law for every choice, and asserting the bound for every choice is the stronger reading
--   - encoding: "For all β > β_c − δ"; "for all β < β_c + δ" → 0 < β added to both clauses; reason: the random-cluster model and π̂ are defined for β > 0 (p.4, p.22); this only excludes parameters where the laws are undefined
--   - encoding: "For integers ℓ, R, r ≥ 0" in (26), with R = C log n/log log n; whp over G ∼ G_n → R real, tree excess (an integer) compared with R; ℓ = ⌈C′ log n⌉₊; natural log; WithHighProb d; reason: the theorem itself sets R to a real value; G_n is the uniform d-regular ensemble G_{n,d} of the section
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 21, p.23 (restated p.42, proved in §7)

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_LowTempGlauber_Supplement_RandomCluster
import Definitions.Def_LowTempGlauber_Supplement_Lifted

open Classical

namespace LowTempGlauber.Supplement

open PottsRapidMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…7533d), Theorem 21, p.23 (restated p.42, proved in §7).

Let `d ≥ 3` be an integer and `q > 2` real. For the small constant `θ > 0` of `H^±_θ` and any
sufficiently small `δ > 0` and any `D > 0`, there are constants `C, C' > 0` and an integer `r ≥ 1` such
that whp over `G ∼ G_{n,d}`, with `R = C log n / log log n` and `ℓ = ⌈C' log n⌉`:
for all `β > β_c − δ`, `Pr[(ω, ω') ∈ A_{G,R} ∪ B_{G,ℓ,r} ∪ H⁺_θ] ≤ n^{−D}` for independent
`ω, ω' ∼ π̂⁺`; and for all `β < β_c + δ` the same holds for `π̂⁻` with `H⁻_θ`.

**Formalization Note.**
* "For some small constant `θ > 0`" (p.23, before the theorem) is `∃ θ > 0`; "for any sufficiently
  small `δ > 0`" is `∃ δ₀ > 0, ∀ δ ∈ (0, δ₀)`; `C, C', r` come after `δ, D` and before the whp event;
  `β` is quantified inside the whp event (the bound is uniform in `β`, p.43), with `β > 0` (the model's
  range, p.4).
* `C₁(ω)`, "the largest component", is any choice `c` of a maximum-size component of `(V, F)`
  (`IsLargestChoice`), quantified inside the whp event: the bound holds for every tie-break.
* `R` is real, `ℓ = ⌈C' log n⌉₊` (`Nat.ceil`), `log` natural. Whp is the published `WithHighProb d`
  (`G_n` = `G_{n,d}`). -/
theorem theorem_21 (d : ℕ) (hd : 3 ≤ d) (q : ℝ) (hq : 2 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ D : ℝ, 0 < D →
      ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∃ r : ℕ, 1 ≤ r ∧
        WithHighProb d (fun n G =>
          (∀ β : ℝ, 0 < β → betaC q d - δ < β →
            ∀ c : (G.edgeSet → Bool) → Finset (Fin n), IsLargestChoice G c →
              pairProb (liftPlus G β q d c)
                  (fun ω ω' => EventA G (C * Real.log n / Real.log (Real.log n)) ω ω' ∨
                    EventB G ⌈C' * Real.log n⌉₊ r ω ω' ∨ HPlus d q θ ω ω')
                ≤ (n : ℝ) ^ (-D)) ∧
          (∀ β : ℝ, 0 < β → β < betaC q d + δ →
              pairProb (liftMinus G β q d)
                  (fun ω ω' => EventA G (C * Real.log n / Real.log (Real.log n)) ω ω' ∨
                    EventB G ⌈C' * Real.log n⌉₊ r ω ω' ∨ HMinus d q θ ω ω')
                ≤ (n : ℝ) ^ (-D))) := by sorry

end LowTempGlauber.Supplement
