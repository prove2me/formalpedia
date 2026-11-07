-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_B_4
-- name    : OnlineBinCover.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:51.420415+00:00
-- url     : https://prove2.me/theorems/be6aa267-bb9f-41cf-b528-1fa1231654dc
-- title:
--   Lemma B.4 — the event $\mathcal E$ holds with probability $1-O(K)e^{-\Omega(p\varepsilon\mathrm{vol}(I)^{1/3})}$
-- statement:
--   Fix $\varepsilon$ before sampling, $K=\lceil\varepsilon^{-2}\rceil$, and let $I_p$ be the uniform sample of $\lfloor pn\rfloor$ items. In the ranges of App. B ($p=\Omega(\mathrm{vol}(I)^{-1/20})$, $\varepsilon=\Theta(\mathrm{vol}(I)^{-1/24})$, $\mathrm{vol}(I)$ sufficiently large): for all $c_1,c_2,c_3>0$ there are $C,c>0$ and $V_0$ such that for every instance with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge V_0$, every $p\in[c_1\mathrm{vol}(I)^{-1/20},1]$ and every $\varepsilon\in[c_2\mathrm{vol}(I)^{-1/24},c_3\mathrm{vol}(I)^{-1/24}]$,
--
--   $$\Pr\big[\text{three-class case}\Rightarrow\mathcal E\big]\ge1-CK\exp\!\big(-c\,p\,\varepsilon\,\mathrm{vol}(I)^{1/3}\big),$$
--
--   where $\mathcal E$ is the event that the sample volume and all cutoffs $R_1,\dots,R_K,R_M$ of Definition 3.1 are within the stated distances of their means.
--
--   On $\mathcal E$ every group and the medium class of the input have the size the sample predicts, which drives the slot-covering arguments.
--
--   Differences from the source:
--   - encoding: standing ranges $p=\Omega(\mathrm{vol}(I)^{-1/20})$, $\varepsilon=\Theta(\mathrm{vol}(I)^{-1/24})$, $\mathrm{vol}(I)$ sufficiently large (App. B, p.18) → for all $c_1,c_2,c_3>0$ there are constants and $V_0$ such that the bound holds for $p\in[c_1\mathrm{vol}(I)^{-1/20},1]$, $\varepsilon\in[c_2\mathrm{vol}(I)^{-1/24},c_3\mathrm{vol}(I)^{-1/24}]$, $\mathrm{vol}(I)\ge V_0$; reason: the paper's asymptotic standing assumption made explicit; $\varepsilon<1/8$ follows for large $V_0$
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: a uniformly random subset of $\lfloor pn\rfloor$ items → the first $\lfloor pn\rfloor$ arrivals of a uniform permutation, probability the fraction of the $n!$ permutations; reason: the same law
--   - encoding: "whenever the thresholds in Definition 3.1 are constructed" → the three-class case of the sample classification implies $\mathcal E$; reason: the thresholds are constructed exactly in that case
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
--   - reading: the sampling fraction $p$ (Algorithm 2's input; $I_p$ has $\lfloor pn\rfloor$ items of $I$) → $0<p\le1$; reason: a sampling fraction of the input; this is the range the paper uses (App. B.6 takes $p<1$)
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.4, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_OnlineBinCover_EventE
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Lemma B.4, p.21. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Standing ranges of App. B (p.18): `p = Ω(vol(I)^{-1/20})`, `ε = Θ(vol(I)^{-1/24})` fixed before
sampling, `vol(I)` sufficiently large. For all constants `c₁, c₂, c₃ > 0` there are `C, c, V₀` such
that, for every instance with sizes in `(0, 1]` and `vol(I) ≥ V₀`, every `p ∈ [c₁ vol^{-1/20}, 1]` and
every `ε ∈ [c₂ vol^{-1/24}, c₃ vol^{-1/24}]`, with probability at least
`1 − C K exp(−c p ε vol(I)^{1/3})` over the sample of `⌊pn⌋` items, the event `E` holds whenever the
thresholds of Definition 3.1 are constructed (the three-class case). -/
theorem lemma_B_4 : ∀ c₁ c₂ c₃ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ →
    ∃ C c V₀ : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → V₀ ≤ vol s → ∀ p ε : ℝ,
      c₁ * vol s ^ (-(1 : ℝ) / 20) ≤ p → p ≤ 1 →
      c₂ * vol s ^ (-(1 : ℝ) / 24) ≤ ε → ε ≤ c₃ * vol s ^ (-(1 : ℝ) / 24) →
      1 - C * (Kof ε : ℝ) * Real.exp (-(c * p * ε * vol s ^ ((1 : ℝ) / 3))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          ThreeClass s (smp σ ⌊p * n⌋₊) ε → EventE s (smp σ ⌊p * n⌋₊) ε p) := by sorry

end OnlineBinCover
