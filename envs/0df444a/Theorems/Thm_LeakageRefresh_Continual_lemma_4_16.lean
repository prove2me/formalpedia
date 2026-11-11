-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_16
-- name    : LeakageRefresh.Continual.lemma_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:40.897429+00:00
-- url     : https://prove2.me/theorems/5c275f37-944d-4658-bd6a-22168c77a6b7
-- title:
--   Lemma 4.16 — changing one encoding between signed rounds: $\mathbb E_{A,B}\|F_{A,B}\|_*\le8/\beta$ and label change $\le8\,\mathrm{disc}_n/\beta$ ($4$ and $4\,\mathrm{disc}_n$ at an endpoint)
-- statement:
--   Let $n\ge2$, $q=2^n-1$, $\mathrm{disc}_n=3/\sqrt{q-1}$ and $\beta>0$. Let $G$ (round $j$) and $G'$ (round $j+1$) be tables on $U_L^2\times U_R^2$ with product representations whose energies satisfy the bounds (4.59)–(4.62): $\Phi,\Psi\le2/\beta$ pointwise and $\mathbb E\Phi,\mathbb E\Psi\le4$. For states $A=X_{j-1}$, $B=X_{j+1}$ put $F_{A,B}(X)=G(A,X)\cdot G'(X,B)$, a table in the two shares of $X$. For every pair of labels $(s_A,s_B)$, with $A\leftarrow\mu_{s_A}$ and $B\leftarrow\mu_{s_B}$ independent,
--   $$\mathbb E_{A,B}\big[\|F_{A,B}\|_*\big]\le\frac8\beta, \tag{4.66}$$
--   $$\mathbb E_{A,B}\Big[\big|\mathbb E_{X\leftarrow\mu_0}F_{A,B}(X)-\mathbb E_{X\leftarrow\mu_1}F_{A,B}(X)\big|\Big]\le\frac{8\,\mathrm{disc}_n}{\beta}. \tag{4.67}$$
--   At a chain endpoint, with one incident signed round ($F_A(X)=G(A,X)$ when $X$ is the last state, $F_B(X)=G'(X,B)$ when it is the first), the bounds are $4$ and $4\,\mathrm{disc}_n$.
--
--   Differences from the source:
--   - generalization: $G_j$, $G_{j+1}$ the approximations of Lemma 4.13, with $\beta=q^{-1/3}$ → any tables with product representations satisfying (4.59)–(4.62), for any $\beta>0$; reason: the proof uses only these energy bounds; Lemma 4.13's tables with $\beta=q^{-1/3}$ satisfy them, so the statement specializes to the paper's
--   - encoding: "at a chain endpoint, with just one incident signed round" → two further conjuncts: $\mathbb E_A\|G(A,\cdot)\|_*\le4$ with the label-change bound $4\,\mathrm{disc}_n$, and the same for $G'(\cdot,B)$; reason: the two possible endpoints (last state, first state) written out
--   - encoding: $\mathbb E_{A,B}$, $\mathbb E_{X\leftarrow\mu_s}$ → finite sums weighted by the point probabilities `mu n s`; reason: expectations over finite distributions written as weighted sums
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 43, Lemma 4.16

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.16 (Changing one encoding between signed rounds).** Let `G` (round `j`) and `G′`
(round `j + 1`) be tables on `U_L² × U_R²` with product representations whose energies satisfy
(4.59)–(4.62): pointwise at most `2/β`, mean at most `4`. For `A = X_{j−1} ←$ µ_{s_A}`,
`B = X_{j+1} ←$ µ_{s_B}` independent and `F_{A,B}(X) = G(A, X) · G′(X, B)` as a table in the two
shares of `X`: (4.66) `E_{A,B}‖F_{A,B}‖_* ≤ 8/β` and (4.67)
`E_{A,B}|E_{X←µ₀}F_{A,B}(X) − E_{X←µ₁}F_{A,B}(X)| ≤ 8 · disc_n/β`. At a chain endpoint (one
incident signed round, `F_A(X) = G(A, X)` or `F_B(X) = G′(X, B)`) the bounds are `4` and
`4 · disc_n`. -/
theorem lemma_4_16 (n : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 < β) (G G' : Table4 n)
    (R : ProdRep G) (R' : ProdRep G')
    (hΦ : ∀ x, R.Φ x ≤ 2 / β) (hΨ : ∀ y, R.Ψ y ≤ 2 / β) (hΦm : avg R.Φ ≤ 4)
    (hΨm : avg R.Ψ ≤ 4)
    (hΦ' : ∀ x, R'.Φ x ≤ 2 / β) (hΨ' : ∀ y, R'.Ψ y ≤ 2 / β) (hΦm' : avg R'.Φ ≤ 4)
    (hΨm' : avg R'.Ψ ≤ 4) :
    (∀ sA sB : ZMod 2,
      ∑ A : State n, ∑ B : State n, mu n sA A * mu n sB B *
          nuclearNorm (fun (ℓ : UL n) (r : UR n) => G (A.1, ℓ) (A.2, r) * G' (ℓ, B.1) (r, B.2)) ≤
        8 / β ∧
      ∑ A : State n, ∑ B : State n, mu n sA A * mu n sB B *
          |muExp n 0 (fun X => G (A.1, X.1) (A.2, X.2) * G' (X.1, B.1) (X.2, B.2)) -
            muExp n 1 (fun X => G (A.1, X.1) (A.2, X.2) * G' (X.1, B.1) (X.2, B.2))| ≤
        8 * disc n / β) ∧
    (∀ sA : ZMod 2,
      ∑ A : State n, mu n sA A * nuclearNorm (fun (ℓ : UL n) (r : UR n) => G (A.1, ℓ) (A.2, r)) ≤ 4 ∧
      ∑ A : State n, mu n sA A *
          |muExp n 0 (fun X => G (A.1, X.1) (A.2, X.2)) -
            muExp n 1 (fun X => G (A.1, X.1) (A.2, X.2))| ≤ 4 * disc n) ∧
    (∀ sB : ZMod 2,
      ∑ B : State n, mu n sB B * nuclearNorm (fun (ℓ : UL n) (r : UR n) => G' (ℓ, B.1) (r, B.2)) ≤ 4 ∧
      ∑ B : State n, mu n sB B *
          |muExp n 0 (fun X => G' (X.1, B.1) (X.2, B.2)) -
            muExp n 1 (fun X => G' (X.1, B.1) (X.2, B.2))| ≤ 4 * disc n) := by sorry

end LeakageRefresh.Continual
