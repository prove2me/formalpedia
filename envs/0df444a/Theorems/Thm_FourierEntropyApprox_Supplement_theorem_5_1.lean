-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_5_1
-- name    : FourierEntropyApprox.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:09:30.116081+00:00
-- url     : https://prove2.me/theorems/879b46a4-abab-43e5-b80b-3984ca62b33d
-- title:
--   Theorem 5.1 — $Q^{*,cc}_\varepsilon(M)\ge c_\varepsilon H_{u,v}(M)$, and $Q^{*,cc}_\varepsilon(M_f)\ge c_\varepsilon\mathbb H(\widehat f^2)$ for XOR functions
-- statement:
--   Let $X,Y$ be finite nonempty sets and $M\in\{-1,1\}^{X\times Y}$ a total sign matrix. $Q^{*,cc}_\varepsilon(M)$ is the least worst-case number of qubits communicated by a two-party quantum protocol, with arbitrary finite-dimensional prior entanglement and local ancillas and with Bob as the output party, that outputs $M_{xy}$ with error at most $\varepsilon$ on every input $(x,y)$. For probability vectors $u,v$, $H_{u,v}(M)$ is the entropy of the squared singular values of $D_{\sqrt u}MD_{\sqrt v}$.
--
--   For every $0\le\varepsilon<1/2$ there is a constant $c_\varepsilon>0$ such that:
--
--   1. for every $X,Y$, every total sign matrix $M$ and every pair of probability vectors $u,v$,
--   $$Q^{*,cc}_\varepsilon(M)\ge c_\varepsilon\,H_{u,v}(M);$$
--   2. for every Boolean $f:\{-1,1\}^n\to\{-1,1\}$ and its XOR matrix $M_f(x,y)=f(x\oplus y)$, where $x\oplus y$ is coordinatewise multiplication,
--   $$Q^{*,cc}_\varepsilon(M_f)\ge c_\varepsilon\,\mathbb H(\widehat f^2).$$
--
--   The constant does not depend on the dimensions of $M$ or on the weights. The bound removes the dimension-dependent denominator of the Linial–Shraibman estimate, and makes Fourier entropy a lower bound on bounded-error quantum communication for XOR functions even with shared entanglement.
--
--   **Formalization Note** Protocols are the published `PermInvCC.EntQProtocol`: an arbitrary input-independent start state on $W$ qubits, alternating messages that move qubits from sender to receiver, local unitaries on held qubits, and Bob measuring an output qubit (`true` = $+1$); the cost is the total number of qubits sent. Each lower bound on $Q^{*,cc}_\varepsilon$ is stated as a bound on the cost of every protocol with error at most $\varepsilon$ on every input.
--
--   Differences from the source:
--   - encoding: $Q^{*,cc}_\varepsilon(M)\ge c_\varepsilon H_{u,v}(M)$ (a bound on the minimum cost) → every protocol with error at most ε on every input has cost ≥ c·H; reason: $Q^{*,cc}_\varepsilon$ is the minimum of these costs over a nonempty set (Alice can send her whole input), so the two forms are equivalent
--   - encoding: two-party protocol with arbitrary finite-dimensional prior entanglement and local ancillas, Bob outputs, cost = qubits communicated → PermInvCC.EntQProtocol with Alice speaking at even-numbered messages; reason: a message may move zero qubits, so fixing the alternation loses nothing; entanglement and ancillas are the arbitrary start state on finitely many qubits
--   - reading: “there is a constant $c_\varepsilon>0$ … In particular … $Q^{*,cc}_\varepsilon(M_f)\ge c_\varepsilon\mathbb H(\widehat f^2)$” → one constant c, chosen before X, Y, M, u, v, n, f, serves both clauses; reason: the page uses the same symbol $c_\varepsilon$ in both clauses, the second being the special case $u,v$ uniform
--   - encoding: $x\oplus y$, coordinatewise multiplication on $\{-1,1\}^n$ → coordinatewise xor on Fin n → Bool; reason: the base encoding true = −1 turns multiplication of signs into xor; same matrices
--   - encoding: finite non-empty sets $X,Y$, $M\in\{-1,1\}^{X\times Y}$, Boolean $f:\{-1,1\}^n\to\{-1,1\}$ → X Y : Type with Fintype and Nonempty, a real matrix M with every entry 1 or −1, real-valued f on Fin n → Bool with IsBoolean f; reason: every finite set is in bijection with a finite type, and the base mission's conventions; same matrices and functions
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 5.1, p.21 (PDF p.21); model and (30)–(32), p.20

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_Supplement_Huv
import Definitions.Def_PermInvCC_EntQProtocol

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 5.1.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.21:
"For every 0 ≤ ε < 1/2, there is a constant c_ε > 0 such that, for every total sign matrix M and every pair of
probability vectors u, v, Q*,cc_ε(M) ≥ c_ε H_{u,v}(M). In particular, for f : {−1, 1}ⁿ → {−1, 1}, let
M_f(x, y) = f(x ⊕ y), u and v be uniform distributions, and then we have Q*,cc_ε(M_f) ≥ c_ε ℍ(f̂²)."
Model, p.20: "X, Y finite non-empty sets … M ∈ {−1, 1}^{X×Y} a total sign matrix. The quantity Q*,cc_ε(M) is
the minimum worst-case number of qubits communicated by a two-party protocol that outputs M_xy with error at
most ε on every input (x, y). Arbitrary finite-dimensional prior entanglement and local ancillas are allowed.
Bob is the designated output party."

**Formalization Note.**
* Protocols are the published `PermInvCC.EntQProtocol`: qubit-ownership model, arbitrary input-independent
  start state (prior entanglement and ancillas), local unitaries on held qubits, Bob measures the output qubit
  (`true` = `+1`), cost = total number of qubits sent. `P.errQ x y b` is the probability of an output other
  than `b`; the correct output on `(x, y)` is `decide (M x y = 1)`.
* `Q*,cc_ε(M) ≥ c_ε H` is stated in its equivalent universal form: every protocol computing `M` with error
  at most `ε` on every input has cost at least `c_ε H` (`Q*,cc_ε` is the minimum of these costs over a
  nonempty set: Alice can send her whole input).
* `c_ε` depends on `ε` only: it is chosen before `X`, `Y`, `M`, `u`, `v`, `n`, `f`, and the same
  constant serves both clauses. `X`, `Y` are finite nonempty types; `u`, `v` are arbitrary probability
  vectors (zero entries allowed). `H_{u,v}(M)` is `Huv u v M`.
* XOR clause: `x ⊕ y` (coordinatewise multiplication on `{−1, 1}ⁿ`) is coordinatewise `xor` on the base
  encoding `Cube n = Fin n → Bool`; `ℍ(f̂²)` is `entropyFun f`. -/
theorem theorem_5_1 :
    ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y]
        (M : Matrix X Y ℝ), (∀ x y, M x y = 1 ∨ M x y = -1) →
        ∀ (u : X → ℝ) (v : Y → ℝ), (∀ x, 0 ≤ u x) → ∑ x, u x = 1 → (∀ y, 0 ≤ v y) → ∑ y, v y = 1 →
        ∀ P : PermInvCC.EntQProtocol X Y, (∀ x y, P.errQ x y (decide (M x y = 1)) ≤ ε) →
          c * Huv u v M ≤ (P.cost : ℝ)) ∧
      (∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
        ∀ P : PermInvCC.EntQProtocol (Cube n) (Cube n),
          (∀ x y, P.errQ x y (decide (f (fun i => xor (x i) (y i)) = 1)) ≤ ε) →
          c * entropyFun f ≤ (P.cost : ℝ)) := by sorry

end Supplement

end FourierEntropyApprox
