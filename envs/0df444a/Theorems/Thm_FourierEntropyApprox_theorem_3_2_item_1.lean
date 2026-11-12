-- Prove2me | Theorems.Thm_FourierEntropyApprox_theorem_3_2_item_1
-- name    : FourierEntropyApprox.theorem_3_2_item_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:46:18.519122+00:00
-- url     : https://prove2.me/theorems/a72d6e0a-439c-4c71-b7cd-e9e815dbcbeb
-- title:
--   Proof of Theorem 3.2, item 1: majority amplification, $|f-P_t|\le 2e^{-t\delta^2/2}$ (margin form)
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be Boolean, let $\delta>0$, and let $P:\{-1,1\}^n\to\mathbb R$ satisfy, at every $x$,
--
--   $$|P(x)|\le 1\qquad\text{and}\qquad f(x)P(x)\ge\delta .$$
--
--   Let $P_t=\mathrm{Maj}_t(P,\dots,P)$ be the multilinear composition of majority on $t$ variables with $P$. Then for every $t\ge0$,
--
--   $$\|f-P_t\|_\infty\le 2e^{-t\delta^2/2}\qquad\text{and hence}\qquad \|f-P_t\|_2^2\le 4e^{-t\delta^2}.$$
--
--   In the paper, $P=3P'/4$ for a $1/3$-approximating polynomial $P'$ of $f$; then $|P|\le1$ and $fP\ge1/2$, and $\delta=1/2$ gives the printed bounds $\|f-P_t\|_\infty\le2e^{-t/8}$ and $\|f-P_t\|_2^2\le4e^{-t/4}$. This is the amplification step that turns one coarse approximant into a sequence of approximants of every accuracy.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is written pointwise. $P_t$ is `majCompose t P`, with ties of $\mathrm{Maj}_t$ at even $t$ going to $+1$.
--
--   Differences from the source:
--   - generalization: $P=3P'/4$ for a $1/3$-approximating $P'$ (so $|P|\le1$, $fP\ge1/2$), with bounds $2e^{-t/8}$, $4e^{-t/4}$ → any real $P$ with $|P|\le1$ and $fP\ge\delta>0$, with bounds $2e^{-t\delta^2/2}$, $4e^{-t\delta^2}$; reason: $\delta=1/2$ gives the printed item, since $3P'/4$ satisfies both hypotheses; the margin form is what makes the paper's "without loss of generality $\varepsilon=1/3$" cover $1/3<\varepsilon<1$ ($P=P'/(1+\varepsilon)$, $\delta=(1-\varepsilon)/(1+\varepsilon)$)
--   - generalization: $t\ge1$ variables → every $t\in\mathbb N$, including $t=0$; reason: $P_0\equiv1$ and $|f-1|\le2=2e^0$, so the case adds nothing false and the statement specializes to $t\ge1$
--   - reading: $\mathrm{Maj}_t$ at even $t$, tie rule unstated → ties go to $+1$; reason: the page uses even $t=4j+8$; the bound holds for either tie value, since the error event is a deviation of at least $t\delta$ from the mean in both cases
--   - encoding: $\mathrm{Maj}_t(P,\dots,P)$ → the multilinear expansion of $\mathrm{Maj}_t$ evaluated at $(P(x),\dots,P(x))$; $\|\cdot\|_\infty$ → a bound at every $x$; reason: the paper's meaning of the composition; same values
--   - encoding: $\{-1,1\}^n$, $S\subseteq[n]$ → `Fin n → Bool` with true ↦ −1, `Finset (Fin n)`; reason: same points and sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), proof of Theorem 3.2, item 1, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_majCompose

namespace FourierEntropyApprox

/-- **Proof of Theorem 3.2, item 1 (majority amplification), in margin form.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.15:
"1. ‖f − P_t‖_∞ ≤ 2e^{−t/8}, and hence ‖f − P_t‖₂² ≤ 4e^{−t/4}", for `P = 3P′/4` with `P′` a 1/3-approximating
polynomial of the Boolean `f` and `P_t = Maj_t(P, …, P)`.

Let `f` be Boolean and `P` a real function on the cube with `|P(x)| ≤ 1` and `f(x)P(x) ≥ δ > 0` at every `x`.
Then for every `t`, `|f(x) − P_t(x)| ≤ 2e^{−tδ²/2}` at every `x`, and `‖f − P_t‖₂² ≤ 4e^{−tδ²}`.

**Formalization Note.** The page's `P = 3P′/4` satisfies `|P| ≤ 1` and `fP ≥ 1/2`, and `δ = 1/2` gives the
printed constants `2e^{−t/8}` and `4e^{−t/4}`. The margin form also covers `P = P′/(1+ε)`,
`δ = (1−ε)/(1+ε)` for an `ε`-approximating `P′`. `‖·‖_∞` is written pointwise. `P_t` is `majCompose t P`,
the multilinear expansion of `Maj_t` (ties to `+1`) at `(P(x), …, P(x))`; `t = 0` is included. -/
theorem theorem_3_2_item_1 {n : ℕ} (f P : Cube n → ℝ) (δ : ℝ) (hf : IsBoolean f) (hδ : 0 < δ)
    (hP : ∀ x, |P x| ≤ 1) (hfP : ∀ x, δ ≤ f x * P x) (t : ℕ) :
    (∀ x, |f x - majCompose t P x| ≤ 2 * Real.exp (-((t : ℝ) * δ ^ 2) / 2)) ∧
      l2NormSq (f - majCompose t P) ≤ 4 * Real.exp (-((t : ℝ) * δ ^ 2)) := by sorry

end FourierEntropyApprox
