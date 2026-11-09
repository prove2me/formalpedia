-- Prove2me | Theorems.Thm_GoodQLTC_main_theorem_good_qltc
-- name    : GoodQLTC.main_theorem_good_qltc
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:34.306356+00:00
-- url     : https://prove2.me/theorems/b6f17e17-aed5-4189-9de0-27acc3ec169b
-- title:
--   Main Theorem: asymptotically good quantum locally testable codes
-- statement:
--   There are constants $r,\delta,\sigma>0$ and $w\in\mathbb N_{\ge1}$, and binary CSS codes $\{Q_\nu\}$ of lengths $N_\nu\to\infty$, such that
--   $$
--   K(Q_\nu)\ge rN_\nu,\qquad d(Q_\nu)\ge\delta N_\nu,\qquad H_\nu\succeq\frac{\sigma}{N_\nu}D_{Q_\nu}.
--   $$
--   Every check has weight at most $w$, and every qubit belongs to at most $w$ checks. The check matrices can be constructed in time polynomial in $N_\nu$.
--
--   Here $Q_\nu$ is given by $H_X^\nu\in\mathbb F_2^{m_X\times N_\nu}$, $H_Z^\nu\in\mathbb F_2^{m_Z\times N_\nu}$ with $H_X^\nu(H_Z^\nu)^{\top}=0$; $K$ is the number of logical qubits, $d=\min\{d_X,d_Z\}$ the distance, $H_\nu$ the average rejecting projection of the full check list and $D_{Q_\nu}$ the quantum Hamming-distance operator; the soundness inequality holds on the whole Hilbert space.
--
--   **Formalization Note** The constants precede $\nu$; the polynomial-time clause is one Turing machine and one polynomial for all $\nu$.
--
--   Differences from the source:
--   - encoding: families indexed by ν ≥ 1 → families indexed by ν ∈ ℕ; reason: index shift; same instances
--   - encoding: N ≥ 1 (H_N is defined for N ≥ 1) and m = m_X + m_Z ≥ 1 ((3.1)) → 1 ≤ N_ν and 1 ≤ m_X + m_Z stated for every ν; reason: the conventions under which K, d, H and D_Q are defined
--   - encoding: d(Q_ν) ≥ δN_ν with d ∈ ℕ ∪ {∞} → ENNReal.ofReal(δN_ν) ≤ d(Q_ν); reason: same inequality for finite and infinite d
--   - encoding: the check matrices can be constructed in time polynomial in N_ν → one TM2 machine, input ν in unary, output the injective encoding of (N_ν, m_X, m_Z, H_X^ν, H_Z^ν), running time ≤ p(N_ν) for one polynomial p; reason: Lemma 14.2: deterministic algorithm, input the level ν, time polynomial in N_ν
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Main Theorem, p.3 (PDF p.6); restated as Theorem 4.14, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_GoodQLTC_IsCSS
import Definitions.Def_GoodQLTC_logicalQubits
import Definitions.Def_GoodQLTC_cssDist
import Definitions.Def_GoodQLTC_IsLocallyTestable
import Definitions.Def_GoodQLTC_IsPolyTimeInBlocklength

namespace GoodQLTC

/-- **Main Theorem** (restated as Theorem 4.14), Gay–Jeronimo, *Asymptotically Good Quantum
Locally Testable Codes*, arXiv:2609.20780 (held version), p.3 (Theorem 4.14, p.19): there are
constants `r, δ, σ > 0` and `w ∈ ℕ_{≥1}`, and binary CSS codes `{Q_ν}` of lengths `N_ν → ∞`, such
that `K(Q_ν) ≥ r N_ν`, `d(Q_ν) ≥ δ N_ν`, `H_ν ⪰ (σ/N_ν) D_{Q_ν}`. Every check has weight at most
`w`, and every qubit belongs to at most `w` checks. The check matrices can be constructed in time
polynomial in `N_ν`.

**Formalization Note.** `r, δ, σ, w` are chosen before `ν`. `Q_ν` is given by binary check matrices
`H_X^ν ∈ F_2^{m_X(ν) × N_ν}`, `H_Z^ν ∈ F_2^{m_Z(ν) × N_ν}` with `H_X^ν (H_Z^ν)^⊺ = 0`; every row is
a listed check; `N_ν ≥ 1` and `m_X + m_Z ≥ 1` are the conventions of §3 (`H_N` for `N ≥ 1`, (3.1)).
`K` is `N − rank H_X − rank H_Z`, `d = min{d_X, d_Z} ∈ ℕ∞` with `min ∅ = +∞`, soundness is the
Loewner inequality on the whole Hilbert space (`IsLocallyTestable` also carries the check weights
`≤ w`), and the qubit degree counts the X- and Z-checks touching the qubit. The last sentence is
one Turing machine with input `ν` in unary and one polynomial `p` with running time `≤ p(N_ν)`
(`IsPolyTimeInBlocklength`). The family is indexed by `ν ∈ ℕ`. -/
theorem main_theorem_good_qltc :
    ∃ (r δ σ : ℝ) (w : ℕ), 0 < r ∧ 0 < δ ∧ 0 < σ ∧ 1 ≤ w ∧
    ∃ (N mX mZ : ℕ → ℕ) (HX : ∀ ν, Matrix (Fin (mX ν)) (Fin (N ν)) (ZMod 2))
      (HZ : ∀ ν, Matrix (Fin (mZ ν)) (Fin (N ν)) (ZMod 2)),
      Filter.Tendsto N Filter.atTop Filter.atTop ∧
      (∀ ν, 1 ≤ N ν ∧ 1 ≤ mX ν + mZ ν ∧ IsCSS (HX ν) (HZ ν) ∧
        r * (N ν : ℝ) ≤ (logicalQubits (HX ν) (HZ ν) : ℝ) ∧
        ENNReal.ofReal (δ * (N ν : ℝ)) ≤ ((cssDist (HX ν) (HZ ν) : ℕ∞) : ENNReal) ∧
        IsLocallyTestable w σ (HX ν) (HZ ν) ∧
        ∀ i, qubitDegree (HX ν) (HZ ν) i ≤ w) ∧
      IsPolyTimeInBlocklength N (fun ν => cssData (HX ν) (HZ ν)) := by sorry

end GoodQLTC
