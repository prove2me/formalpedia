-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_lemma_c_2
-- name    : MuonLastIterate110.Stochastic.lemma_c_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:03.295652+00:00
-- url     : https://prove2.me/theorems/33e979be-f713-4422-9df0-799b2eecaee2
-- title:
--   Lemma C.2 — inexact-input descent
-- statement:
--   Suppose Assumption 3.1 holds, fix a finite $J\ge1$, $\varepsilon\ge0$ and a step $\eta>0$, and put $B=u_J$. Let $W$ be the current iterate, $g=\nabla F(W)$, $N$ an input of the Newton–Schulz map, $D=\Phi_\varepsilon(N)$, $r=N-g$, and let $W^+=W-\eta D$ be the update (3.3), with $g^+=\nabla F(W^+)$. Then
--
--   $$
--   \langle g,D\rangle\ge\ell_J\psi_\varepsilon(\|g\|)-(\ell_J+B)\|r\|,
--   $$
--
--   $$
--   F(W^+)\le F(W)-\ell_J\eta\,\psi_\varepsilon(\|g\|)+(\ell_J+B)\eta\|r\|+\frac{LB^2}{2}\eta^2,
--   $$
--
--   and the gradient norm cannot change too quickly:
--
--   $$
--   \bigl|\,\|g^+\|-\|g\|\,\bigr|\le LB\eta .
--   $$
--
--   With $W=W_t$, $N=N_t$, $\eta=\eta_t$ these are (C.6)–(C.8) for the Muon update. They are the per-step estimates behind the summability criterion of Theorem C.1.
--
--   Differences from the source:
--
--   - generalization: the Muon update (3.3) at time t, with N_t from (3.1)–(3.2) and η_t > 0 → any current point W, any Newton–Schulz input N and any step η > 0, with W⁺ = W − ηΦ_ε(N); reason: the source's proof uses only (3.3) and Lemma 3.2; taking W = W_t, N = N_t, η = η_t gives the source's statement
--   - encoding: real m×n matrices with Frobenius norm ‖X‖_F and inner product tr(XᵀY) → EuclideanSpace ℝ (Fin m × Fin n), read as a matrix through toMat for the products of (3.4); reason: the Euclidean norm and inner product on this type are exactly the Frobenius ones (checked in the sanity file); same instances
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.21, Lemma C.2, (C.6)–(C.8); proof p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Muon

open scoped RealInnerProductSpace

namespace MuonLastIterate110.Stochastic

/-- Lemma C.2 (Inexact-input descent), p.21. Under Assumption 3.1, for a finite `J ≥ 1`, any
`ε ≥ 0` and any step `η > 0`: let `W` be the current iterate, `g = ∇F(W)`, `N` any input of the
Newton–Schulz map, `D = Φ_ε(N)`, `r = N − g`, the next iterate `W⁺ = W − ηD` of (3.3) and
`g⁺ = ∇F(W⁺)`. With `B = u_J`, (C.6), (C.7) and (C.8) hold. Applied to `W = W_t`, `N = N_t`,
`η = η_t` this is the source's statement for the Muon update. -/
theorem lemma_c_2 {m n : ℕ} (F : Mat m n → ℝ) (L Finf : ℝ) (hF : Assumption31 F L Finf)
    (J : ℕ) (hJ : 1 ≤ J) (ε : ℝ) (hε : 0 ≤ ε) (η : ℝ) (hη : 0 < η) (W N : Mat m n) :
    ellJ J * psi ε ‖gradient F W‖ - (ellJ J + uJ J) * ‖N - gradient F W‖
        ≤ ⟪gradient F W, Phi J ε N⟫ ∧
    F (W - η • Phi J ε N) ≤ F W - ellJ J * η * psi ε ‖gradient F W‖
        + (ellJ J + uJ J) * η * ‖N - gradient F W‖ + L * uJ J ^ 2 / 2 * η ^ 2 ∧
    |‖gradient F (W - η • Phi J ε N)‖ - ‖gradient F W‖| ≤ L * uJ J * η := by sorry

end MuonLastIterate110.Stochastic
