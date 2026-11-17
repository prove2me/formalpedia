-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_5
-- name    : LinMaxLoad.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:26:51.255602+00:00
-- url     : https://prove2.me/theorems/0ba063b3-f1b1-423d-acc6-566e313c9184
-- title:
--   Theorem 5 / Lemma 9 — $m(S) \le 1 + p^{\ell-u} - p^{-u} + (1-p^{-\ell})\sum_{\gamma\ne0}|\hat S(\gamma)| \le 2 + \|\hat S\|_1$
-- statement:
--   Let $p$ be a prime, $S \subseteq \mathbb F_p^u$, and $\ell = \lceil \log_p |S| \rceil$.
--
--   1. (Lemma 9) If $S$ is nonempty, then
--   $$
--   m(S) \le 1 + p^{-u+\ell} - p^{-u} + (1 - p^{-\ell}) \sum_{\gamma \ne 0} |\hat S(\gamma)| \le 2 + \sum_{\gamma \in \mathbb F_p^u} |\hat S(\gamma)| .
--   $$
--   2. (Theorem 5) For every $S$,
--   $$
--   m(S) \le 2 + \|\hat S\|_1, \qquad \|\hat S\|_1 = \sum_{\gamma \in \mathbb F_p^u} |\hat S(\gamma)| .
--   $$
--
--   Here $m(S)$ is the expected linear max load and $\hat S(\gamma) = p^{-u}\sum_{x \in S} \chi_\gamma(x)$ is the Fourier coefficient of the indicator of $S$. Since a set of coset complexity $k$ has Fourier 1-norm at most $k$, sets of bounded coset complexity have bounded expected linear max load.
--
--   Differences from the source:
--   - encoding: $\mathbb F_p^u$; $m(S)$ with $\ell = \lceil\log_p |S|\rceil$; $\hat S$; $p^{-u+\ell}$ → `Fin u → ZMod p`; published `linMaxLoad` with `Nat.clog p S.card`; `fourierCoeff`; integer powers `zpow`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Lemma 9, p.24 (Theorem 5, p.6)

import Mathlib
import Definitions.Def_LinMaxLoad_linMaxLoad
import Definitions.Def_LinMaxLoad_Supplement_fourierCoeff

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 5** (p.6), formal statement **Lemma 9** (p.24), of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Lemma 9: let `S ⊆ F_p^u` be a nonempty set. Then
`m(S) ≤ 1 + p^{−u+ℓ} − p^{−u} + (1 − p^{−ℓ}) Σ_{γ≠0} |Ŝ(γ)| ≤ 2 + Σ_{γ ∈ F_p^u} |Ŝ(γ)|`.
Theorem 5: for `S ⊆ F_p^u`, `m(S) ≤ 2 + ‖Ŝ‖₁`.

**Formalization Note** `ℓ = ⌈log_p |S|⌉` (`Nat.clog p S.card`, the `ℓ` of `m(S)`), `m(S)` is the
published `linMaxLoad` and `Ŝ` is `fourierCoeff` (normalized by `p^{−u}`). Both inequalities of
Lemma 9's chain are stated for nonempty `S`, and Theorem 5's `m(S) ≤ 2 + ‖Ŝ‖₁` for every `S`
(including `S = ∅`, as Theorem 5 allows). Powers of `p` with integer exponents are `zpow`. -/
theorem theorem_5 (p : ℕ) [Fact p.Prime] (u : ℕ) (S : Finset (Fin u → ZMod p)) :
    (S.Nonempty →
      linMaxLoad p u S ≤ 1 + (p : ℝ) ^ ((Nat.clog p S.card : ℤ) - u) - (p : ℝ) ^ (-(u : ℤ)) +
          (1 - (p : ℝ) ^ (-(Nat.clog p S.card : ℤ))) *
            ∑ γ ∈ Finset.univ.filter (fun γ : Fin u → ZMod p => γ ≠ 0), ‖fourierCoeff p u S γ‖ ∧
      1 + (p : ℝ) ^ ((Nat.clog p S.card : ℤ) - u) - (p : ℝ) ^ (-(u : ℤ)) +
          (1 - (p : ℝ) ^ (-(Nat.clog p S.card : ℤ))) *
            ∑ γ ∈ Finset.univ.filter (fun γ : Fin u → ZMod p => γ ≠ 0), ‖fourierCoeff p u S γ‖
        ≤ 2 + ∑ γ : Fin u → ZMod p, ‖fourierCoeff p u S γ‖) ∧
    linMaxLoad p u S ≤ 2 + ∑ γ : Fin u → ZMod p, ‖fourierCoeff p u S γ‖ := by sorry

end LinMaxLoad.Supplement
