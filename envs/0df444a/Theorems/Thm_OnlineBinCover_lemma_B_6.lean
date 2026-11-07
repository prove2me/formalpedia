-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_B_6
-- name    : OnlineBinCover.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:58.16547+00:00
-- url     : https://prove2.me/theorems/36f1299b-6364-4056-8d48-9329888e873e
-- title:
--   Lemma B.6 — comparing the medium-item cutoffs
-- statement:
--   In the ranges of App. B and under its standing assumption $R'_M<n$ (p.23): for all $c_1,c_2,c_3>0$ there are $C>0$ and $V_0$ such that, for every instance with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge V_0$, every $p,\varepsilon$ in the ranges and every sample $I_p$ of $\lfloor pn\rfloor$ items in the three-class case, on $\mathcal E$:
--
--   1. $M'\subseteq M$, and every item of $M'$ is at least as large as every item of $S'$;
--   2. $t'_M\ge t_M$;
--   3. $|S'\setminus S|\le C\,\mathrm{vol}(I)^{2/3}/\varepsilon$;
--   4. $S_p\subseteq S'_p=I_p\cap S'$;
--   5. for every feasible solution of the configuration LP (3) on the sample,
--   $$|M'|\ge\mathrm{ALG}_{BP}(I)-C\,\frac{\mathrm{vol}(I)^{2/3}}{\varepsilon}.\qquad(6)$$
--
--   The deterministic cutoff $t'_M$ replaces the random cutoff $t_M$, so that a concentration bound can be applied to the fixed set $S'$.
--
--   Differences from the source:
--   - encoding: standing ranges $p=\Omega(\mathrm{vol}(I)^{-1/20})$, $\varepsilon=\Theta(\mathrm{vol}(I)^{-1/24})$, $\mathrm{vol}(I)$ sufficiently large (App. B, p.18) → for all $c_1,c_2,c_3>0$ there are constants and $V_0$ such that the bound holds for $p\in[c_1\mathrm{vol}(I)^{-1/20},1]$, $\varepsilon\in[c_2\mathrm{vol}(I)^{-1/24},c_3\mathrm{vol}(I)^{-1/24}]$, $\mathrm{vol}(I)\ge V_0$; reason: the paper's asymptotic standing assumption made explicit; $\varepsilon<1/8$ follows for large $V_0$
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: "We may assume $R^\prime_M<n$" (p.23, before the lemma) → hypothesis $R^\prime_M<n$; reason: a standing assumption of App. B.3; the other case has zero S-slot demands
--   - generalization: $\mathrm{ALG}_{BP}(I)$ of the blueprint built from the LP solution of Lemma 2.2 → every feasible LP solution on the sample; reason: (6) uses Observation 3.2, which needs feasibility only
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
--   - reading: the sampling fraction $p$ (Algorithm 2's input; $I_p$ has $\lfloor pn\rfloor$ items of $I$) → $0<p\le1$; reason: a sampling fraction of the input; this is the range the paper uses (App. B.6 takes $p<1$)
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.6, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_OnlineBinCover_EventE
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Lemma B.6 (Comparing the medium-item cutoffs), p.23. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Standing ranges of App. B as in Lemma B.4 and the standing assumption `R′_M < n` of App. B.3 (p.23).
On `E` (three-class case): `M′ ⊆ M`, every item of `M′` is at least as large as every item of `S′`,
`t′_M ≥ t_M`, `|S′ \ S| ≤ C vol(I)^{2/3}/ε`, `Sp ⊆ S′p`, and (6) `|M′| ≥ ALGBP(I) − C vol(I)^{2/3}/ε`
for every feasible solution of LP (3) on the sample. -/
theorem lemma_B_6 : ∀ c₁ c₂ c₃ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ →
    ∃ C V₀ : ℝ, 0 < C ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → V₀ ≤ vol s → ∀ p ε : ℝ,
      c₁ * vol s ^ (-(1 : ℝ) / 20) ≤ p → p ≤ 1 →
      c₂ * vol s ^ (-(1 : ℝ) / 24) ≤ ε → ε ≤ c₃ * vol s ^ (-(1 : ℝ) / 24) →
      ∀ σ : Equiv.Perm (Fin n),
      ThreeClass s (smp σ ⌊p * n⌋₊) ε → EventE s (smp σ ⌊p * n⌋₊) ε p → RMprime s ε < n →
        Mprime s (smp σ ⌊p * n⌋₊) ε ⊆ inputM s (smp σ ⌊p * n⌋₊) ε ∧
        (∀ a ∈ Mprime s (smp σ ⌊p * n⌋₊) ε, ∀ b ∈ Sprime s ε, s b ≤ s a) ∧
        tM s (smp σ ⌊p * n⌋₊) ε ≤ tMprime s ε ∧
        ((Sprime s ε \ inputS s (smp σ ⌊p * n⌋₊) ε).card : ℝ) ≤
          C * vol s ^ ((2 : ℝ) / 3) / ε ∧
        smallOf s (smp σ ⌊p * n⌋₊) ε ⊆ Sprime s ε ∩ smp σ ⌊p * n⌋₊ ∧
        ∀ x : (Fin (Kof ε) → ℕ) →₀ ℝ,
          LPFeasible (lpCnt s (smp σ ⌊p * n⌋₊) ε) (rsize s (smp σ ⌊p * n⌋₊) ε)
            (lpVolS s (smp σ ⌊p * n⌋₊) ε) x →
          (ALGBP x p : ℝ) - C * vol s ^ ((2 : ℝ) / 3) / ε ≤
            ((Mprime s (smp σ ⌊p * n⌋₊) ε).card : ℝ) := by sorry

end OnlineBinCover
