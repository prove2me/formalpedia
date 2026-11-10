-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_gaussian_permanent_anticoncentration
-- name    : GinibrePermanent977.Anticoncentration.gaussian_permanent_anticoncentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:27.509205+00:00
-- url     : https://prove2.me/theorems/41e61a4b-8dfd-4a74-a315-4d23466272fa
-- title:
--   Theorem 1.1 — Gaussian permanent anticoncentration over $\mathbb R,\mathbb C,\mathbb H$
-- statement:
--   Throughout, $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$ with $\beta=\dim_{\mathbb R}\mathbb K\in\{1,2,4\}$; a **standard $\mathbb K$-Gaussian** has independent real coordinates $N(0,1/\beta)$, $G_n^{\mathbb K}$ is an $n\times n$ matrix and $B_n$ an $(n-1)\times n$ matrix of i.i.d. standard $\mathbb K$-Gaussian entries, $\operatorname{per}_{\mathbb K}A=\sum_{\sigma}a_{1\sigma(1)}a_{2\sigma(2)}\cdots a_{n\sigma(n)}$ is the row-ordered permanent, and $(C_n^{\mathbb K})_j=\operatorname{per}_{\mathbb K}((B_n)_{-j})$ is the permanental cofactor column ($C_1^{\mathbb K}=(1)$). Let $W_n^{\mathbb K}=\operatorname{per}_{\mathbb K}G_n^{\mathbb K}/\sqrt{n!}$, $\kappa_{n,\beta}$ the constant of (20), (22) and $\omega_\beta=\pi^{\beta/2}/\Gamma(\beta/2+1)$ the volume of the unit ball of $\mathbb R^\beta$.
--
--   For every $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$ there is a constant $C_\beta>0$, depending only on $\beta$, such that for every $n\ge1$ the random variable $W_n^{\mathbb K}$ has a radial Lebesgue density $p_n^{\mathbb K}$ on $\mathbb K\cong\mathbb R^\beta$ with
--
--   $$
--   \|p_n^{\mathbb K}\|_\infty=p_n^{\mathbb K}(0)\le C_\beta\,n^{(\beta+2)/4}\quad(1),\qquad p_n^{\mathbb K}(z)\le p_n^{\mathbb K}(0)\le\kappa_{n,\beta}\ \ (z\in\mathbb K)\quad(27),
--   $$
--
--   and for every $\varepsilon>0$ and every center $z\in\mathbb K$,
--
--   $$
--   P\bigl(|W_n^{\mathbb K}-z|\le\varepsilon\bigr)\le C_\beta\,n^{(\beta+2)/4}\varepsilon^\beta\quad(2),\qquad
--   P\bigl(|W_n^{\mathbb K}-z|\le\varepsilon\bigr)\le\min\{1,\omega_\beta\kappa_{n,\beta}\varepsilon^\beta\}\quad(28).
--   $$
--
--   For $\mathbb K=\mathbb C$, $\omega_2\kappa_{n,2}=n$, so (28) reads $\sup_zP(|\operatorname{per}G_n-z|\le\varepsilon\sqrt{n!})\le\min\{1,n\varepsilon^2\}$ (29), which is the Permanent Anticoncentration Conjecture of Aaronson and Arkhipov; for $\mathbb K=\mathbb R$ it is its real-Gaussian version.
--
--   **Formalization Note** The density is a measurable $p:\mathbb K\to[0,\infty]$ with $P(W_n^{\mathbb K}\in s)=\int_sp\,d\lambda$ for every Borel set $s$, where the probability is the Ginibre law of the preimage; $\|p\|_\infty$ is the essential supremum for Lebesgue measure $\lambda$. Radial means $p(z)=p(w)$ whenever $|z|=|w|$. One constant serves (1) and (2); the bound $p(0)\le\kappa_{n,\beta}$ makes $p$ finite.
--
--   Differences from the source:
--
--   - encoding: $K\in\{\mathbb R,\mathbb C,\mathbb H\}$ → a tag `F : Scalar` with carriers ℝ, ℂ, ℍ[ℝ] and β = 1, 2, 4; reason: Lean convention selecting the three concrete scalar domains; same instances
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: “$W_n^{\mathbb K}$ has a density $p$”, $\|p\|_\infty$ → measurable $p:\mathbb K\to[0,\infty]$ with $P(W\in s)=\int_s p$ for Borel $s$; `essSup p volume`; reason: definition of a Lebesgue density and of its $L^\infty$ norm
--   - encoding: $\lesssim_\beta$ in (1) and (2), $\sup_{z\in\mathbb K}$ → one constant $C>0$ chosen per scalar domain before $n$, $z$, $\varepsilon$; the bound for every $z$; reason: two implied constants can be replaced by their maximum; a bound for every center is the bound on the supremum
--   - encoding: $\kappa_{n,\beta}$ defined as the limit (20) → `kappa F n` = the closed form (22); reason: (20) = (22) is computed on p. 12; same number for every $n\ge1$
--   - generalization: Theorem 1.1 states (1) and (2) → also asserts the exact bounds (27) $p(z)\le p(0)\le\kappa_{n,\beta}$ and (28) $P(|W-z|\le\varepsilon)\le\min\{1,\omega_\beta\kappa_{n,\beta}\varepsilon^\beta\}$ for the same density; reason: these are proved in the proof of Theorem 1.1 on p. 13; dropping them gives exactly Theorem 1.1
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §1, p. 2, Theorem 1.1, Eqs. (1)–(2); proof §3.5, pp. 13–14, Eqs. (27)–(29); Eqs. (20), (22), p. 12 (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Theorem 1.1 (Gaussian permanent anticoncentration), p. 2, with the exact bounds (27)–(28) of its
proof, p. 13. For every `K ∈ {ℝ, ℂ, ℍ}` there is `C > 0` (depending only on `β = dim_ℝ K`) such
that for every `n ≥ 1`, `W_n^K = per_K G_n^K / √(n!)` has a radial Lebesgue density `p` with
`‖p‖_∞ = p(0) ≤ C n^{(β+2)/4}` (1), `p(z) ≤ p(0) ≤ κ_{n,β}` (27), and for every `ε > 0` and
every center `z ∈ K`, `P(|W_n^K - z| ≤ ε) ≤ C n^{(β+2)/4} ε^β` (2) and
`P(|W_n^K - z| ≤ ε) ≤ min {1, ω_β κ_{n,β} ε^β}` (28). -/
theorem gaussian_permanent_anticoncentration (F : Scalar) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ p : F.K → ℝ≥0∞,
      Measurable p ∧
      (∀ s : Set F.K, MeasurableSet s →
        ginibre F n n (normPer ⁻¹' s) = ∫⁻ z in s, p z) ∧
      (∀ z w : F.K, ‖z‖ = ‖w‖ → p z = p w) ∧
      essSup p volume = p 0 ∧
      p 0 ≤ ENNReal.ofReal (C * (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4)) ∧
      (∀ z : F.K, p z ≤ p 0) ∧
      p 0 ≤ ENNReal.ofReal (kappa F n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ z : F.K,
        ginibre F n n {G | ‖normPer G - z‖ ≤ ε} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4) * ε ^ F.beta) ∧
          ginibre F n n {G | ‖normPer G - z‖ ≤ ε} ≤
            ENNReal.ofReal (min 1 (omegaBall F * kappa F n * ε ^ F.beta)) := by sorry

end GinibrePermanent977.Anticoncentration
