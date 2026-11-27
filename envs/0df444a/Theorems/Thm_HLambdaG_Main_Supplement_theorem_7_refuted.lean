-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_7_refuted
-- name    : HLambdaG.Main.Supplement.theorem_7_refuted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:06:29.732591+00:00
-- url     : https://prove2.me/theorems/0d3d7e81-bf3a-4a16-986d-51218232e816
-- title:
--   Theorem 7, p. 643 — corrected disposition: explicit refutation of the printed FCLT and (30)
-- statement:
--   Set $\lambda=g=h=1$, $T_1=T_2=T$ with $T(s)=s+\sqrt s$, and $B(t)=((\sqrt{1+4t}-1)/2)^2$. The continuous cumulative input $F(s,t)=\min(s,B(t))^2$ has finite margins $s^2,B(t)^2$. Its averages (1) are $G(s)=s$ and $H(t)=B(t)^2/t$. The inverse is $S_1=S_2=B$, and both remainders (28) vanish. With exactly the printed scaling (27), uniformly on bounded time intervals,
--   $$
--   G_n\to0,\quad T_n^1=T_n^2\to\sqrt t,\quad S_n^1=S_n^2\to-\sqrt t,\quad H_n\to-2\sqrt t.
--   $$
--   Thus Theorem 7 is false as printed. Its relation $H(t)=G(t)-T(t)$ would give $-\sqrt t$, and its equality in distribution $S(t)=^dT(t)$ would identify $-\sqrt t$ with $\sqrt t$.
--
--   **Formalization Note** The Lean item states the concrete input's monotonicity and finite marginal limits, the continuous time change and its generalized inverse, exact saturation (so both remainders are zero), compact convergence and the contradictions at time one. Deterministic compact convergence to continuous limits implies J₁ weak convergence on a singleton probability space. There is no reinterpretation of $G,H$ as cumulative quantities; this refutes the literal source and does not purport to state a repaired general FCLT. The two numeric discrepancies at time one are $-1\ne1$ and $-2\ne-1$.
--
--   Differences from the source:
--
--   - correction: Theorem 7 asserts FCLT transfer and the limit identities (30) → an explicit deterministic refutation of the printed result, using the averages (1) literally in (27); reason: with F(s,t)=min(s,B(t))² and T(s)=s+√s both remainders are zero, while G_n→0, T_n→√t, S_n→−√t, H_n→−2√t; (30) instead requires S =ᵈ √t and H=−√t
-- source:
--   Glynn and Whitt, Oper. Res. 37 (1989), p. 643, Theorem 7 and displays (27)–(30)

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_FCLTExamples

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Refutation of Theorem 7 as printed, including (27) with G,H as the averages (1).
Take λ = g = h = 1, F(s,t) = min(s,B(t))², T₁ = T₂ = s + √s, S₁ = S₂ = B.
The remainders vanish; G(s) = s. All paths are deterministic, so convergence uniformly
on compact intervals to continuous limits implies the required J₁ weak convergence.
The actual limits S = -√t, H = -2√t refute both the '=ᵈ' claim S =ᵈ T and the
transformation H = G - T in (30). No cumulative reinterpretation of G or H is used. -/
theorem theorem_7_refuted :
    Continuous curvedT ∧ Monotone curvedT ∧ Tendsto curvedT atTop atTop ∧
    Continuous curvedS ∧ Monotone curvedS ∧
    (∀ t : ℝ≥0, curvedS t = sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < s + Real.sqrt s}) ∧
    (∀ t : ℝ≥0, Monotone (fun s => curvedF s t) ∧
      Tendsto (fun s => curvedF s t) atTop (𝓝 ((curvedS t) ^ 2))) ∧
    (∀ s : ℝ≥0, Monotone (curvedF s) ∧
      Tendsto (curvedF s) atTop (𝓝 ((s : ℝ) ^ 2))) ∧
    (∀ s : ℝ≥0, curvedS (⟨curvedT s, by unfold curvedT; positivity⟩ : ℝ≥0) = s ∧
      curvedF s ⟨curvedT s, by unfold curvedT; positivity⟩ = (s : ℝ) ^ 2) ∧
    CompactConvergence (diffusion (fun s => (s : ℝ))) (fun _ => 0) ∧
    CompactConvergence (diffusion curvedT) (fun t => Real.sqrt t) ∧
    CompactConvergence (diffusion curvedS) (fun t => -Real.sqrt t) ∧
    CompactConvergence (diffusion curvedH) (fun t => -2 * Real.sqrt t) ∧
    (-Real.sqrt (1 : ℝ) ≠ Real.sqrt (1 : ℝ)) ∧
    (-2 * Real.sqrt (1 : ℝ) ≠ 0 - Real.sqrt (1 : ℝ)) := by sorry

end HLambdaG.Main.Supplement
