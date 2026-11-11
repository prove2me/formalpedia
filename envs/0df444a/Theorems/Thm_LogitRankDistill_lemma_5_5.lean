-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_5
-- name    : LogitRankDistill.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:45.078726+00:00
-- url     : https://prove2.me/theorems/6d360850-ca81-4240-8673-2335c5af137e
-- title:
--   Lemma 5.5 — with distributional spanners at every step the program (14a)–(14c) is feasible with probability 1 − ηt
-- statement:
--   Fix $t\in[T]$, sets $\hat F_s\subset\tilde F_s=\hat F_s\cup(\Sigma\circ\hat F_{s+1})\subset\Sigma^{\le T-s+1}$ for $s\in[t+1]$, and vectors $L_{s,i}=L_{\mathrm{oracle}}(h_{s,i}\circ\cdot)$ on $\tilde F_s$ ($i\in[\bar d]$, $\bar d\ge1$, $h_{1,i}$ empty, $h_{s,i}\in\Sigma^{s-1}$) as in Algorithm 1, with $\beta=2$ (§5.2). If $L_{s,1:\bar d}$ is an $(\eta,\beta)$-distributional spanner for the law $P_s$ of $L^\star_s=(L_{\mathrm{oracle}}(y_{1:s-1}\circ f))_{f\in\tilde F_s}$, $y\sim M$, for each $s\in[t]$, then
--   $$\Pr_{y_{1:t}\sim M}\big[\text{the program (14a)–(14c) at }y_{1:t}\text{ is infeasible}\big]\le\eta\,t .$$
--   It controls the failure mass of Algorithm 2 in the proof of Theorem 5.11 (Eq. (30)).
--
--   **Formalization Note.** The oracle $O$ is arbitrary; the program's vectors are passed with their values on $\tilde F_s$; the probability is the outer measure under $M$ of the infeasible set.
--
--   Differences from the source:
--   - reading: "sets … and vectors L_{1:t,1:d̄} as in Algorithm 1" → explicit hypotheses: F̃_s = F̂_s ∪ (Σ ∘ F̂_{s+1}), F̂_s ⊂ Σ^{≤T−s+1}, L_{s,i} = L_oracle(h_{s,i} ∘ ·) with |h_{s,i}| = s − 1, d̄ ≥ 1; reason: these are the properties Algorithm 1 guarantees (Lines 3, 5, 7)
--   - reading: β of the program, unspecified in the lemma → β = 2; reason: standing parameter setting of §5.2 (p. 23); with β < 1 the constraint c_1 = e_1 is infeasible
--   - encoding: with probability 1 − η·t the program is feasible → outer measure of the infeasible set ≤ ηt; reason: equivalent formulation
--   - generalization: the ε_apx-approximate oracle of §5.2 for M → any oracle O and any distribution M; reason: the lemma uses only the distributional-spanner hypothesis; the §5.2 oracle is a special case
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 25, Lemma 5.5

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

open MeasureTheory

namespace LogitRankDistill

/-- **Lemma 5.5** (p. 25): fix `t ∈ [T]`, sets `F̂_s ⊂ F̃_s = F̂_s ∪ (Σ ∘ F̂_{s+1}) ⊂ Σ^{≤T−s+1}`
(`s ∈ [t + 1]`) and vectors `L_{s,i} = L_oracle(h_{s,i} ∘ ·)` on `F̃_s` as in Algorithm 1
(`h_{1,i}` empty, `h_{s,i} ∈ Σ^{s−1}`, `i ∈ [d̄]`, `d̄ ≥ 1`; `β = 2` as in §5.2). If `L_{s,1:d̄}` is
an `(η, β)`-distributional spanner for `P_s` (the law of `(L_oracle(y_{1:s−1} ∘ f))_{f ∈ F̃_s}`,
`y ∼ M`) for each `s ∈ [t]`, then with probability at least `1 − η t` over `y_{1:t} ∼ M` the
program (14a)–(14c) is feasible. -/
theorem lemma_5_5 {Tok : Type*} [Fintype Tok] [DecidableEq Tok] [MeasurableSpace Tok]
    [MeasurableSingletonClass Tok] {T : ℕ} (M : PMF (Fin T → Tok)) (O : List Tok → Tok → ℝ)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (Fhat : ℕ → Finset (List Tok))
    (hF : ∀ s, 1 ≤ s → s ≤ t + 1 → ∀ f ∈ Fhat s, f.length + s ≤ T + 1)
    (dbar : ℕ) (hd : 1 ≤ dbar) (hist : ℕ → ℕ → List Tok)
    (hhist : ∀ s i, (hist s i).length = s - 1) (η β : ℝ) (hβ : β = 2)
    (hspan : ∀ s, 1 ≤ s → s ≤ t →
      IsDistSpanner M.toMeasure (fun x (f : tilde Fhat s) => Lor O (pre x (s - 1) ++ f.1))
        (fun (i : Fin dbar) (f : tilde Fhat s) => Lor O (hist s i ++ f.1)) η β) :
    M.toMeasure {x | ¬ (⟨t, pre x t, Fhat, dbar,
        fun s i f => if f ∈ tilde Fhat s then Lor O (hist s i ++ f) else 0, β⟩ :
          ProgData Tok).InG} ≤ ENNReal.ofReal (η * t) := by sorry

end LogitRankDistill
