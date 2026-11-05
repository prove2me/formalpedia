-- Prove2me | Theorems.Thm_KMSHolder_holder_inequality
-- name    : KMSHolder.holder_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:57.871624+00:00
-- url     : https://prove2.me/theorems/a94f782b-5c03-4eaa-9987-264f1abc695e
-- title:
--   Theorem 2.2, Hölder inequality for KMS states: $|\omega(A_n\Delta^{z_n}\cdots A_1\Delta^{z_1}A_0)| \le \prod_j |||A_j|||_{p_j}$ (corrected: $\sum_j\Re z_j + \frac1{2p_0} + \frac1{2p_n} \le 1$)
-- statement:
--   Let $M$ be a von Neumann algebra on a Hilbert space $H$ with cyclic and separating unit vector $\Omega$, vector state $\omega = \langle\Omega, \cdot\,\Omega\rangle$ and modular operator $\Delta$. (For a $(\tau,\beta)$-KMS state $\omega_\beta$ in its GNS representation, $\Delta = e^{-\beta L}$ with $L$ the Liouvillean, and $\Delta^z = e^{-z\beta L}$.) For positive $A \in M$ and an even integer $p \ge 2$ put
--
--   $$
--   |||A|||_p = \omega\big(A\Delta^{1/p}A\cdots\Delta^{1/p}A\big)^{1/p} \qquad (p \text{ copies of } A),
--   $$
--
--   where $\omega(A_n\Delta^{z_n}\cdots A_1\Delta^{z_1}A_0)$ denotes Araki's multiple-time correlation: the value at $z$ of the analytic continuation of $s \mapsto \langle\Omega, A_n\Delta^{is_n}\cdots A_1\Delta^{is_1}A_0\Omega\rangle$ to the tube $I^{(n)}$ (it exists and is unique, milestone `KMSHolder.araki_continuation_exists_unique`).
--
--   Let $n \ge 1$ and $z = (z_1, \dots, z_n) \in \mathbb C^n$ with $0 \le \Re z_j$ and $\sum_j \Re z_j \le 1$. Let $p_0, \dots, p_n$ be positive even integers with
--
--   $$
--   \frac1{p_j} \le \min\{\Re z_{j+1}, \Re z_j\}, \qquad z_{n+1} = z_n,\ z_0 = z_1,
--   $$
--
--   and
--
--   $$
--   \sum_{j=1}^n \Re z_j + \frac1{2p_0} + \frac1{2p_n} \le 1 .
--   $$
--
--   Then for all positive $A_0, \dots, A_n \in M$,
--
--   $$
--   \big|\omega\big(A_n\Delta^{z_n}\cdots A_1\Delta^{z_1}A_0\big)\big| \le |||A_0|||_{p_0} \cdots |||A_n|||_{p_n}. \qquad (3)
--   $$
--
--   The bound estimates a non-commutative multiple-time correlation by "essentially commutative" quantities computable by spectral theory, uniformly in the imaginary parts $\Im z_j$. For a Gibbs state on a matrix algebra it is the Hölder trace inequality. It is used to construct real-time Green's functions from Schwinger functions in quantum statistical mechanics and thermal Wightman functions in constructive field theory.
--
--   **Formalization Note** The Lean statement takes every continuation $G$ of the correlation of $A_0, \dots, A_n$ and every continuation $G_j$ of the correlation of $p_j$ copies of $A_j$ (with $p_j - 1$ variables), and bounds $|G(z)|$ by $\prod_j |G_j(1/p_j, \dots, 1/p_j)|^{1/p_j}$. The neighbour conditions are `hp_left` ($1/p_j \le \Re z_j$ for $j \ge 1$) and `hp_right` ($1/p_j \le \Re z_{j+1}$ for $j \le n-1$), which with $z_0 = z_1$, $z_{n+1} = z_n$ are the paper's conditions.
--
--   Differences from the source:
--   - correction: $\sum_j \Re z_j \le 1$ → in addition $\sum_j \Re z_j + \frac1{2p_0} + \frac1{2p_n} \le 1$; reason: the printed theorem is false: for $n = 1$, $z_1 = 1$, $p_0 = p_1 = 2$, the Gibbs state $\rho = \mathrm{diag}(0.9, 0.1)$ on $M_2(\mathbb C)$ and $A_0 = A_1 = |v\rangle\langle v|$ with $v = (1,1)/\sqrt2$, the left side is $\mathrm{Tr}(A_1\rho A_0) = 0.5$ and the right side is $\langle v, \rho^{1/2}v\rangle^2 = 0.4$; the proof's last step applies (8) to exponents summing to $\sum_j\Re z_j + \frac1{2p_0} + \frac1{2p_n}$.
--   - generalization: a $(\tau,\beta)$-KMS state on a C*-dynamical system, $e^{-z\beta L}$ → any von Neumann algebra with cyclic separating unit vector, $\Delta^z$; reason: the paper identifies $\Delta^{1/2} = e^{-\beta L/2}$ (pp.2, 4), so a KMS state's GNS data are an instance.
--   - generalization: $p_j$ the smallest positive even integer with $1/p_j \le \min\{\Re z_{j+1}, \Re z_j\}$ → every positive even $p_j$ with these bounds; reason: the smallest one is one such choice.
--   - reading: Araki's symbolic notation → every continuation $G$, $G_j$ with `IsArakiContinuation`; reason: the continuation exists and is unique, so this is the paper's value.
--   - reading: $(\cdot)^{1/p}$ in $|||A|||_p$ → applied to the modulus $|\cdot|$; reason: the value is the nonnegative real $\phi(\mathbb 1)$ (Lemma 4.2), so the instances are the same.
--   - encoding: indices $z_1, \dots, z_n$, $p_0, \dots, p_n$, $A_0, \dots, A_n$; $M^+$; $n \ge 1$ → Lean `z j` = $z_{j+1}$, `Fin (n+1)` for $p$, $A$; `A j ∈ S.M` and `IsPositive`; `1 ≤ n`; reason: Lean convention; the conventions $z_0 = z_1$, $z_{n+1} = z_n$ presuppose $n \ge 1$.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, Theorem 2.2, p.3 (with eq. (2), p.3; proof p.9)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_KMSHolder_tube
import Definitions.Def_KMSHolder_realChain
import Definitions.Def_KMSHolder_IsArakiContinuation

open OAI.BoundedRecovery

namespace KMSHolder

/-- Jäkel–Robl, *The Hölder Inequality for KMS States*, arXiv:1103.3608v2, Theorem 2.2, p.3
(corrected: `Σⱼ ℜzⱼ + 1/(2p₀) + 1/(2pₙ) ≤ 1`):
"Let `(z₁, …, zₙ) ∈ ℂⁿ` be such, that `0 ≤ ℜzⱼ`, `Σⱼ ℜzⱼ ≤ 1`, and let `pⱼ` be the smallest,
positive even integer such that `1/pⱼ ≤ min{ℜzⱼ₊₁, ℜzⱼ}`, with `zₙ₊₁ = zₙ` and `z₀ = z₁`. Then
`|ω_β(Aₙ e^{−zₙβL} ⋯ A₁ e^{−z₁βL} A₀)| ≤ |||A₀|||_{p₀} ⋯ |||Aₙ|||_{pₙ}` (3)
for all `A₀, …, Aₙ ∈ M⁺`", where `|||A|||_p = ω_β(A Δ^{1/p} A ⋯ Δ^{1/p} A)^{1/p}` (`p` copies of
`A`, eq. (2)).

Lean statement: for standard modular data `S`, `n ≥ 1`, `z` with `0 ≤ ℜzⱼ`, `Σ ℜzⱼ ≤ 1`, positive
even `pⱼ` (`j = 0, …, n`) with `1/pⱼ ≤ ℜzⱼ` (`j ≥ 1`) and `1/pⱼ ≤ ℜzⱼ₊₁` (`j ≤ n − 1`), and the
corrected condition `Σ ℜzⱼ + 1/(2p₀) + 1/(2pₙ) ≤ 1`; for positive `Aⱼ ∈ M`, every continuation
`G` of `s ↦ ⟪Ω, AₙΔ^{isₙ} ⋯ Δ^{is₁}A₀Ω⟫` and every continuation `Gⱼ` of the chain of `pⱼ` copies
of `Aⱼ`: `‖G z‖ ≤ ∏ⱼ ‖Gⱼ(1/pⱼ, …, 1/pⱼ)‖^{1/pⱼ}`.

**Formalization Note.**
* Correction: the printed theorem fails at `n = 1`, `z₁ = 1`, `p₀ = p₁ = 2` (Gibbs state
  `ρ = diag(0.9, 0.1)` on `M₂(ℂ)`, `A₀ = A₁ = |v⟩⟨v|`, `v = (1,1)/√2`: left side `0.5`, right side
  `0.4`); the proof's last step applies (8) to exponents summing to `Σℜzⱼ + 1/(2p₀) + 1/(2pₙ)`.
* Standard modular data replace the KMS state; `e^{−zβL}` is `Δ^z`, `Δ^{is} = S.D.unitary s`.
* Every positive even `pⱼ` with the neighbour bounds is allowed, not only the smallest; the
  conventions `z₀ = z₁`, `zₙ₊₁ = zₙ` are built into `hp_left` / `hp_right`.
* Araki's symbolic notation is read through `IsArakiContinuation` (the continuation exists and is
  unique: `KMSHolder.araki_continuation_exists_unique`), so the statement is not vacuous.
* `(·)^{1/p}` is applied to the modulus `‖·‖` (the value is the nonnegative real `φ(1)` of
  Lemma 4.2).
* Indices: `z ⟨j⟩` is the paper's `z_{j+1}`; `p ⟨j⟩`, `A ⟨j⟩` are `pⱼ`, `Aⱼ` (`j = 0, …, n`);
  `Fin.last n` is the index `n`. -/
theorem holder_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ)
    (hz_nonneg : ∀ j, 0 ≤ (z j).re) (hz_sum : ∑ j, (z j).re ≤ 1)
    (p : Fin (n + 1) → ℕ) (hp_even : ∀ j, Even (p j)) (hp_pos : ∀ j, 0 < p j)
    (hp_left : ∀ (j : Fin (n + 1)) (hj : 0 < j.val),
      (1 : ℝ) / (p j : ℝ) ≤ (z ⟨j.val - 1, by omega⟩).re)
    (hp_right : ∀ (j : Fin (n + 1)) (hj : j.val < n),
      (1 : ℝ) / (p j : ℝ) ≤ (z ⟨j.val, hj⟩).re)
    (h_corr : ∑ j, (z j).re + 1 / (2 * (p 0 : ℝ)) + 1 / (2 * (p (Fin.last n) : ℝ)) ≤ 1)
    (A : Fin (n + 1) → H →L[ℂ] H) (hA : ∀ j, A j ∈ S.M) (hApos : ∀ j, (A j).IsPositive)
    (G : (Fin n → ℂ) → ℂ) (hG : IsArakiContinuation S A G)
    (Gp : (j : Fin (n + 1)) → (Fin (p j - 1) → ℂ) → ℂ)
    (hGp : ∀ j, IsArakiContinuation S (fun _ : Fin (p j - 1 + 1) => A j) (Gp j)) :
    ‖G z‖ ≤ ∏ j, ‖Gp j (fun _ => ((1 / (p j : ℝ) : ℝ) : ℂ))‖ ^ ((1 : ℝ) / (p j : ℝ)) := by sorry

end KMSHolder
