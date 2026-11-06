-- Prove2me | Theorems.Thm_IAFTRL_lemma_D_10
-- name    : IAFTRL.lemma_D_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:12.794864+00:00
-- url     : https://prove2.me/theorems/5e65c01b-d3de-42ef-9a3a-d70368ad2990
-- title:
--   Lemma D.10 — the G-optimal mixture is feasible for (2.3) on every history
-- statement:
--   Let $\mathcal A$ be a finite action set in the unit ball of $\mathbb R^d$ ($d\ge1$) spanning $\mathbb R^d$, let $t\ge1$, let $S\in\mathbb R^d$ be any cumulative estimate (with exponential weights $q_t$ and reference action $r_t$), and let $\pi$ be a G-optimal law: a probability vector with $\Sigma(\pi)=\sum_a\pi_aaa^\top\succ0$ and $a^\top\Sigma(\pi)^{-1}a\le d$ for all $a$. Set
--   $$
--   p^0=(1-\Gamma_t)q_t+\Gamma_t\pi .
--   $$
--   Then
--   1. $p^0$ is feasible for the program (2.3) (with the mixture $w^0=\Gamma_t\pi$);
--   2. $\sum_bp^0_b\,v_b(p^0)\,b^\top=I_d$;
--   3. $\sum_bp^0_b\big[(a-r_t)^\top v_b(p^0)\big]^2\le\beta_t$ for every action $a$;
--   4. $C_t(p^0)<2d/\beta_t$.
--
--   So the sampling program is feasible on every history, and $p^0$ is a comparison point for the executed minimizer.
--
--   **Formalization Note** The program depends on the history only through $S=\sum_{s<t}\hat\theta_s$, so the statement is for every $S\in\mathbb R^d$. A G-optimal law exists by Lemma J.3 (the Kiefer–Wolfowitz theorem).
--
--   Differences from the source:
--   - generalization: every finite pre-action history → every cumulative estimate $S\in\mathbb R^d$; reason: the program depends on the history only through $S$ (p.56) and the proof uses only $q_t>0$, $Z_t\ge0$, $\Gamma_t<1/4$, which hold at every $S$
--   - generalization: $\pi$ a G-optimal law → $\pi$ any probability vector with $\Sigma(\pi)\succ0$ and $\max_aa^\top\Sigma(\pi)^{-1}a\le d$; reason: the proof uses only these two properties (D.91); every G-optimal law has them (Lemma J.3)
--   - encoding: constraints (2.3d)–(2.3f) as suprema over feedback laws → their computable forms (pp.18–19); reason: the paper states the equivalence itself
--   - encoding: "with this prescribed mixture" $w^0=\Gamma_t\pi$ → existential mixture in the feasibility predicate; reason: $w^0$ is a witness; (2.3d)–(2.3f) do not depend on $w$
--   - encoding: dimension $d$ of $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball; only the degenerate $d=0$ is excluded
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.4.3, Lemma D.10, p.79

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsGOptLaw
import Definitions.Def_IAFTRL_IsFeasible2_3

namespace IAFTRL

open Matrix

/-- **Lemma D.10 (A feasible physical covariance reconstruction).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.10, p.79:
"For every finite pre-action history, let `π` be a G-optimal law and set `p⁰ = (1 − Γ_t)q_t + Γ_tπ`,
`M = Σ_b p⁰_b bb^⊤`, `w⁰_b = Γ_tπ_b`, and `v⁰_b = v_b(p⁰) = M^{-1}b`. Then `p⁰`, with this prescribed
reconstruction and mixture, satisfies every constraint in (2.3). In particular,
`Σ_b p⁰_b v⁰_b b^⊤ = I_d`, `Σ_b p⁰_b[(a − r_t)^⊤v⁰_b]² ≤ β_t`, `C_t(p⁰) < 2d/β_t`."

For a spanning finite action set in the unit ball of `ℝ^d` (`d ≥ 1`), every paper round `t ≥ 1`,
every cumulative estimate `S` (so every history) and every G-optimal law `π`, the mixture
`p⁰ = (1 − Γ_t)q_t + Γ_tπ` (with `q_t` the exponential weights at `S`):
1. is feasible for (2.3);
2. satisfies `Σ_b p⁰_b v_b(p⁰) b^⊤ = I_d`;
3. satisfies `Σ_b p⁰_b [(a − r_t)^⊤ v_b(p⁰)]² ≤ β_t` for every action `a`;
4. satisfies `C_t(p⁰) < 2d/β_t` (strictly).

**Formalization Note.** "Every finite pre-action history" is generalized to every
`S ∈ ℝ^d`: the program depends on the history only through `S = Σ_{s<t} θ̂_s` (p.56), and the proof
uses only `q_t > 0`, `Z_t ≥ 0` and `Γ_t < 1/4`, which hold at every `S`. The prescribed mixture
`w⁰ = Γ_tπ` is one witness of the existential mixture in `IsFeasible2_3`. -/
theorem lemma_D_10 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (t : ℕ) (ht : 1 ≤ t) (S : Fin d → ℝ) (π : Fin K → ℝ) (hπ : IsGOptLaw arms π) :
    let p0 : Fin K → ℝ := fun b => (1 - Gam d K t) * qSoft (beta d K t) arms S b + Gam d K t * π b
    IsFeasible2_3 arms t S p0 ∧
      ∑ b, p0 b • vecMulVec (vCoef arms p0 b) (arms b) = 1 ∧
      (∀ a, ∑ b, p0 b * ((arms a - refArm arms S) ⬝ᵥ vCoef arms p0 b) ^ 2 ≤ beta d K t) ∧
      proxyC arms t S p0 < 2 * (d : ℝ) / beta d K t := by sorry

end IAFTRL
