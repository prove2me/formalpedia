-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_4_corrected
-- name    : HLambdaG.Main.Supplement.theorem_4_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:04:21.798829+00:00
-- url     : https://prove2.me/theorems/5bd1a0c0-7cd0-4f1c-a0da-c03913f2ce20
-- title:
--   Theorem 4, p. 641 (corrected: inequalities of (i), (ii) reversed in (a), (b); (17) from k = n + 1) — H = λG in the setting of §1.1
-- statement:
--   Consider the setting of §1.1 with one discrete variable, with $G(n)=n^{-1}\sum_{k=1}^nF_k(\infty)$, $H(t)=t^{-1}\sum_{k\ge1}F_k(t)$ and $N(t)=\max\{k\ge0:T_k\le t\}$. Let $0<\lambda<\infty$. Condition (17) is $n^{-1}\sum_{k=n+1}^\infty F_k(T_n)\to0$. "(18) holds" means that some nonnegative finite sequence $\{S_k\}$ satisfies (18).
--
--   (a) Suppose $n^{-1}T_n\to\lambda^{-1}$ and $G(n)\to G$ (finite) as $n\to\infty$.
--
--   1. If (17) holds, then $\displaystyle\limsup_{t\to\infty}H(t)\le\lambda G$.
--   2. If (18) holds, then $\displaystyle\liminf_{t\to\infty}H(t)\ge\lambda G$.
--   3. If (17) and (18) both hold, then $\displaystyle\lim_{t\to\infty}H(t)=\lambda G$.
--
--   (b) Suppose $t^{-1}N(t)\to\lambda$ and $H(t)\to H$ (finite) as $t\to\infty$.
--
--   1. If (17) holds, then $\displaystyle\liminf_{n\to\infty}G(n)\ge\lambda^{-1}H$.
--   2. If (18) holds, then $\displaystyle\limsup_{n\to\infty}G(n)\le\lambda^{-1}H$.
--   3. If (17) and (18) both hold, then $\displaystyle\lim_{n\to\infty}G(n)=\lambda^{-1}H$.
--
--   This is $H=\lambda G$ in the discrete setting, in both directions: from the customer average to the time average in (a), and back in (b). Theorem 5(a) for $L=\lambda W$ is the case (b)1, since (17) always holds there.
--
--   **Formalization Note** The printed parts (i) and (ii) of (a) and (b) have incorrect directions or extrema: (a)(i) $\limsup H\ge\lambda G$, (a)(ii) $\liminf H\le\lambda G$, (b)(i) $\limsup G(n)\le\lambda^{-1}H$, (b)(ii) $\liminf G(n)\ge\lambda^{-1}H$. These follow the interchanged hypotheses of the printed Theorem 1(a), (b) and are false. Two counterexamples, both with $T_k=k$ and $\lambda=1$, refute them. The first is $F_k(t)=1\{t\ge2k\}$: (17) holds, $G\equiv1$ and $H(t)\to\frac12$, which refutes the printed (a)(i) and (b)(i). The second is $F_k(t)=1\{t\ge k/2\}$: (18) holds with $S\equiv0$, $G\equiv1$ and $H(t)\to2$, which refutes the printed (a)(ii) and (b)(ii). The corrected inequalities are those that Theorems 1–3 give. The (iii) parts are as printed. (17) uses the lower index $n+1$ of Theorem 2. $G(n)$ is the published marginal average $G$ of the embedded input at $s=n$, which equals (4). The lim inf and lim sup are taken in the extended reals. All six parts are stated in one theorem.
--
--   Differences from the source:
--
--   - correction: (a)(i) lim sup H ≥ λG; (a)(ii) lim inf H ≤ λG → (a)(i) limsupE H ≤ λG under (17); (a)(ii) λG ≤ liminfE H under (18); reason: printed inequalities follow the interchanged hypotheses of the printed Theorem 1(a)/(b); counterexamples with T_k = k: F_k = 1{t ≥ 2k} ((17) holds, G ≡ 1, H → 1/2) and F_k = 1{t ≥ k/2} ((18) with S ≡ 0, G ≡ 1, H → 2)
--   - correction: (b)(i) lim sup G(n) ≤ λ⁻¹H; (b)(ii) lim inf G(n) ≥ λ⁻¹H → (b)(i) λ⁻¹H ≤ liminf G(n) under (17); (b)(ii) limsup G(n) ≤ λ⁻¹H under (18); reason: same interchange and the same two counterexamples; (b)(i) corrected is what the proof of Theorem 5(a) uses
--   - correction: (17) summed from k = n → Cond17 summed from k = n + 1; reason: the printed index makes Theorem 2 false; see theorem_2_corrected; the printed (17) implies the corrected one
--   - encoding: lim inf / lim sup, possibly infinite → Filter.liminf / Filter.limsup of the EReal coercion (published liminfE / limsupE), with λ multiplied inside the real function; reason: Lean convention; a real lim inf/lim sup of an unbounded function would be a junk value, and EReal keeps the page's possibly infinite values
--   - encoding: s, t ∈ [0, ∞), customers k = 1, 2, … → s, t : ℝ≥0; customers indexed by ℕ with a dummy index 0 (F_0 = 0); reason: Lean convention; the index 0 carries no customer and every sum starts at k = 1, so no instance changes
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 641, Theorem 4 (a)(i)–(iii), (b)(i)–(iii); conditions (17), (18) p. 640; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 4, p. 641, with the inequalities of (a)(i), (a)(ii), (b)(i), (b)(ii) corrected
(the printed parts interchange the roles of (17) and (18), as Theorem 1(a)/(b) do), and (17)
taken with lower index `n + 1` (Theorem 2). Setting of §1.1, `F(s, t) = Σ_{k ≤ [s]} F_k(t)`. -/
theorem theorem_4_corrected (D : DiscreteSetting) (lam : ℝ) (hlam : 0 < lam) :
    -- (a): `n⁻¹T_n → λ⁻¹` and `G(n) → g`
    (∀ g : ℝ, Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop (𝓝 lam⁻¹) →
      Tendsto (fun n : ℕ => G D.input (n : ℝ≥0)) atTop (𝓝 g) →
        (D.Cond17 → limsupE (H D.input) ≤ ((lam * g : ℝ) : EReal)) ∧
        ((∃ S, D.Cond18 S) → ((lam * g : ℝ) : EReal) ≤ liminfE (H D.input)) ∧
        (D.Cond17 → (∃ S, D.Cond18 S) → Tendsto (H D.input) atTop (𝓝 (lam * g)))) ∧
    -- (b): `t⁻¹N(t) → λ` and `H(t) → h`
    (∀ h : ℝ, Tendsto (fun t : ℝ≥0 => (D.N t : ℝ) / (t : ℝ)) atTop (𝓝 lam) →
      Tendsto (H D.input) atTop (𝓝 h) →
        (D.Cond17 → ((lam⁻¹ * h : ℝ) : EReal) ≤
          Filter.liminf (fun n : ℕ => ((G D.input (n : ℝ≥0) : ℝ) : EReal)) atTop) ∧
        ((∃ S, D.Cond18 S) →
          Filter.limsup (fun n : ℕ => ((G D.input (n : ℝ≥0) : ℝ) : EReal)) atTop ≤
            ((lam⁻¹ * h : ℝ) : EReal)) ∧
        (D.Cond17 → (∃ S, D.Cond18 S) →
          Tendsto (fun n : ℕ => G D.input (n : ℝ≥0)) atTop (𝓝 (lam⁻¹ * h)))) := by sorry

end HLambdaG.Main.Supplement
