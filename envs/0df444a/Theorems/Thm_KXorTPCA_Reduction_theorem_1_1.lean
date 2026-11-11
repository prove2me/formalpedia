-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_theorem_1_1
-- name    : KXorTPCA.Reduction.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:22:44.608034+00:00
-- url     : https://prove2.me/theorems/1110e73b-8e3a-47ae-bd3e-3fda22981a28
-- title:
--   Theorem 1.1 — hardness of k-XOR near its computational threshold implies hardness of Tensor PCA at its threshold (detection and exact/weak/strong recovery)
-- statement:
--   In **planted noisy $k$-XOR** $k$-XOR$(n,m,\delta)$ one observes $m$ equations $(\alpha_j,Y_j)$ with $\alpha_j$ uniform $k$-subsets of $[n]$ (i.i.d.) and $Y_j=x_{\alpha_j}W_j$, $W_j\sim\mathrm{Rad}(\delta)$; in **Tensor PCA** $k'$-TensorPCA$(N,\delta)$ one observes $Y=\delta x^{\otimes k'}+G$ with $G$ a symmetric tensor of $N(0,1)$. Both have a secret $x\in\{\pm1\}$ and a null model with the signal replaced by random signs.
--
--   For every integer $k'\ge2$ and every $\varepsilon\in(0,1)$ there is $k_0$ such that for every $k\ge k_0$ and every $\eta>0$ there are a constant $C\ge0$ and a sequence $\delta^{\mathrm{tpca}}(N)$ with
--
--   $$N^{-k'/4-\eta}(\log N)^{-C}\ \le\ \delta^{\mathrm{tpca}}(N)\ \le\ N^{-k'/4-\eta}(\log N)^{C}\qquad(N\ge2)$$
--
--   such that, with $m=\lfloor n^{k(1+\varepsilon)/2}\rfloor$ and $\delta^{\mathrm{xor}}=n^{-k\varepsilon/4-\eta/2}$:
--
--   - **(detection)** for every $c\in[0,1]$: if no polynomial-time program solves detection for $k$-XOR$(n,m,\delta^{\mathrm{xor}})$ with asymptotic Type I + II error at most $c$, then none does for $k'$-TensorPCA$(N,\delta^{\mathrm{tpca}}(N))$;
--   - **(recovery)** for each of exact, weak and strong recovery: if no polynomial-time program solves it for $k$-XOR$(n,m,\delta^{\mathrm{xor}})$, then none solves it for $k'$-TensorPCA$(N,\delta^{\mathrm{tpca}}(N))$.
--
--   Both input and output sit just inside the conjectured computational thresholds $m\delta^2\asymp n^{k/2}$ and $\delta\asymp N^{-k'/4}$, so sparse $k$-XOR near the canonical density transfers its conjectured hardness to Tensor PCA.
--
--   Differences from the source:
--   - reading: "for some sufficiently large $k=k(k',\varepsilon)$" → there is $k_0(k',\varepsilon)$ such that the statement holds for every $k\ge k_0$ and every $\eta>0$; reason: $k$ depends on $(k',\varepsilon)$ only; "every large $k$" is the stronger of the two readings.
--   - reading: $\delta^{\mathrm{tpca}}=\tilde\Theta(n^{-k'/4-\eta})$ → there are $C\ge0$ and one sequence within $(\log N)^{\pm C}$ of $N^{-k'/4-\eta}$ for $N\ge2$, $N$ the Tensor PCA dimension; reason: the reduction produces one such sequence (Lemma 8.1's proof: $\delta'=\tilde\Theta(n'^{-k'\rho'/4-\eta})$).
--   - reading: $m=n^{k(1+\varepsilon)/2}$ → $\lfloor n^{k(1+\varepsilon)/2}\rfloor$; reason: $m$ is real.
--   - reading: "polynomial-time algorithm" → one program of the randomized real RAM halting within $Cn^r+C$ steps on every input of dimension $n$ and every tape; reason: the paper fixes no machine.
--   - reading: "solving detection" → for every $c\in[0,1]$, $\limsup$ of the Type I + II error (null error plus worst-case planted error) at most $c$, the implication holding for each $c$; reason: Definition C.2 parametrizes by the asymptotic error.
--   - reading: "solving recovery" → each of exact, weak and strong recovery (Definitions C.7, C.8), up to global sign, worst case over $x$, success probability tending to $1$; reason: Definitions C.7/C.8 leave the success probability open.
--   - encoding: instances → memory images (k-XOR: dimension, count, sorted index blocks with values; Tensor PCA: dimension and all $N^{k'}$ entries in lexicographic order); reason: the paper fixes no encoding.
--   - encoding: symmetric Gaussian tensor and Tensor PCA null → one $N(0,1)$ per multiset shared by all orderings; null $\delta w_\beta+G_\beta$ with one uniform sign per multiset; reason: Eq. (2) and Remark 1.2.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 2 (PDF 5), Theorem 1.1; derivation pp. 64–66 (PDF 67–69), Corollaries 12.1, 12.2; p. 26 (PDF 29), Lemma 6.4; pp. 24–25 (PDF 27–28), Corollary 6.1; pp. 97–98 (PDF 100–101), Lemmas C.1–C.3

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Tasks

open Real

namespace KXorTPCA.Reduction

theorem theorem_1_1 :
    ∀ k' : ℕ, 2 ≤ k' → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ η : ℝ, 0 < η →
    ∃ (C : ℝ) (δtpca : ℕ → ℝ), 0 ≤ C ∧
      (∀ N : ℕ, 2 ≤ N →
        (N : ℝ) ^ (-(k' : ℝ) / 4 - η) * Real.log N ^ (-C) ≤ δtpca N ∧
        δtpca N ≤ (N : ℝ) ^ (-(k' : ℝ) / 4 - η) * Real.log N ^ C) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ 1 →
        (¬ ∃ A : Program, PolyTime A ∧
            SolvesDetection A (kModel (Choices.std .xor) k ε η) c) →
        ¬ ∃ B : Program, PolyTime B ∧
            SolvesDetection B (fun N => tpcaTask k' N (δtpca N) false) c) ∧
      (∀ notion : RecoveryNotion,
        (¬ ∃ A : Program, PolyTime A ∧
            SolvesRecovery notion A (kModel (Choices.std .xor) k ε η)) →
        ¬ ∃ B : Program, PolyTime B ∧
            SolvesRecovery notion B (fun N => tpcaTask k' N (δtpca N) false)) := by sorry

end KXorTPCA.Reduction
