-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_lemma_C_2
-- name    : KXorTPCA.Reduction.lemma_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:41.381192+00:00
-- url     : https://prove2.me/theorems/8e63ec69-4658-4575-b469-5d135ec6c0f3
-- title:
--   Lemma C.2 — a recovery reduction transfers a recovery algorithm back, with success probability at least 1 − ρ_n − ψ_{n^c}
-- statement:
--   Let $P=(P_n)$, $Q=(Q_n)$ be sequences of planted problems (given by measurable samplers) with losses $\ell_n$, $\ell'_n$ (taken up to global sign), thresholds $\ell^\star_n$, $\ell'^\star_n$ and loss maps $f_n$; let $c>0$ and $d(n)\le n^c$. Let $R$ and $\mathrm{Rec}$ run in time $C_Rn^r+C_R$ and, for every $n$, form an average-case reduction for recovery (Definition C.5) from $P_n$ to $Q_{d(n)}$ with TV-error $\rho_n$. Let $B$ run in time $C_Bn^t+C_B$ and, for every $n'$ and every secret $x'$, achieve loss at most $\delta_{n'}$ (with $0\le\delta_{n'}\le\ell'^\star_{n'}$) with probability at least $1-\psi_{n'}$ on $Q_{n'}$. Then there are a program $A$ and a constant $C$ such that $A$ runs in time $C(n^{ct}+n^r)+C$ and, for every $n$ and every secret $x$,
--
--   $$\mathbb P_{Y\sim(P_n)_x}\Big[\min\big(\ell_n(x,A(Y)),\ell_n(-x,A(Y))\big)\le f_n(\delta_{d(n)})\Big]\ \ge\ 1-\rho_n-\psi_{d(n)},\qquad f_n(\delta_{d(n)})\le\ell^\star_n .$$
--
--   This is the algorithm-transfer property of an average-case reduction for recovery.
--
--   Differences from the source:
--   - generalization: $n'=n^c$ → any dimension map with $d(n)\le n^c$; reason: the proof uses only the running time of $B$ at $d(n)\le n^c$; $d(n)=\lfloor n^c\rfloor$ is the source's case.
--   - reading: Definition C.5(2), whose estimate $\hat x'$ is not quantified → the transfer clause of the mission's Definition C.5 (for every program $B$ producing $\hat x'$, success probability at each threshold transfers up to the TV-error); reason: the printed clause is ambiguous; this is how the lemma and §C.4 use it.
--   - reading: "solves the recovery problem for Q with probability at least $1-\psi_n$" → for every $n'$ and every secret $x'$, loss up to sign at most $\delta_{n'}\in[0,\ell'^\star_{n'}]$ with probability at least $1-\psi_{n'}$; reason: Definitions C.3, C.7, C.8 (worst case over the secret).
--   - reading: $O(n^r)$, $O(n^t)$, $O(n^{ct}+n^r)$-time → explicit worst-case bounds (real exponents $r,t$); one constant pair $(C_R,r)$ for both $R$ and $\mathrm{Rec}$; reason: the machine model of the mission (one common bound is no restriction).
--   - encoding: algorithms → programs of the randomized real RAM; $\mathrm{Rec}$ reads $\hat x'$ from the negative memory cells and sees the reduction's tapes; reason: the paper fixes no machine.
--   - encoding: the problems $P$, $Q$ → samplers from random tapes, assumed measurable; reason: a distribution is the law of a measurable sampler (a non-measurable sampler has no law, and its push-forward would be the zero measure).
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 97 (PDF 100), Lemma C.2

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem lemma_C_2 (P Q : (n : ℕ) → Task n) (d : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hd : ∀ n, (d n : ℝ) ≤ (n : ℝ) ^ c)
    (hPm : ∀ n, Measurable (P n).null ∧ ∀ x, Measurable ((P n).planted x))
    (hQm : ∀ n, Measurable (Q n).null ∧ ∀ x, Measurable ((Q n).planted x))
    (ℓ ℓ' : (n : ℕ) → Signal n → Signal n → ℝ) (ℓstar ℓ'star : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (R Rec : Program) (r : ℝ) (Cr : ℕ)
    (hR : ∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
      HaltsWithin R y ω ((Cr : ℝ) * (n : ℝ) ^ r + Cr))
    (hRec : ∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
      HaltsWithin Rec y ω ((Cr : ℝ) * (n : ℝ) ^ r + Cr))
    (ρs : ℕ → ℝ) (σ : (n : ℕ) → SigMap n (d n))
    (hred : ∀ n, IsRecReduction R Rec (P n) (Q (d n)) (ρs n) (σ n) (ℓ n) (ℓ' (d n))
      (ℓstar n) (ℓ'star (d n)) (f n))
    (B : Program) (t : ℝ) (Cb : ℕ)
    (hB : ∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
      HaltsWithin B y ω ((Cb : ℝ) * (n : ℝ) ^ t + Cb))
    (ψs δs : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δs n ∧ δs n ≤ ℓ'star n)
    (hsucc : ∀ (n : ℕ) (x' : Signal n), 1 - ψs n ≤
      prob2 (fun ω₁ ω₂ => upToSign (ℓ' n) x' (outVec B n ((Q n).planted x' ω₁) ω₂) ≤ δs n)) :
    ∃ (A : Program) (C : ℝ),
      (∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
        HaltsWithin A y ω (C * ((n : ℝ) ^ (c * t) + (n : ℝ) ^ r) + C)) ∧
      ∀ (n : ℕ) (x : Signal n),
        1 - ρs n - ψs (d n) ≤
          prob2 (fun ωi ωa => upToSign (ℓ n) x (outVec A n ((P n).planted x ωi) ωa) ≤
            f n (δs (d n))) ∧
        f n (δs (d n)) ≤ ℓstar n := by sorry

end KXorTPCA.Reduction
