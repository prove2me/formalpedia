-- Prove2me | Theorems.Thm_ModFormPIR_Supplement_main_theorem_5_3
-- name    : ModFormPIR.Supplement.main_theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:48:18.10169+00:00
-- url     : https://prove2.me/theorems/787b2830-b60d-418f-a467-f48d1565911c
-- title:
--   Main Theorem 5.3 — $q$-server PIR with exponent $\eta_{\mathcal L}$ for every even lattice of determinant $\sqrt q$, and $s$-server exponent $\tfrac12+\tfrac{0.467+o(1)}{\log_2 s}$
-- statement:
--   Let $q$ be an odd prime and $\mathcal L\subseteq\mathbb R^r$ an even lattice of determinant $\sqrt q$. For a coset $c\in\mathcal L^*/\mathcal L$ let $w_{\mathcal L}(c)=\frac q2\min_{y\in c}\langle y,y\rangle$, and
--
--   $$\eta_{\mathcal L}=\frac1{\ln q}\inf_{0<t\le1}\Big(\ln\sum_{c\in\mathcal L^*/\mathcal L}t^{w_{\mathcal L}(c)}-\frac{r(q+1)}{24}\ln t\Big).$$
--
--   Then:
--
--   1. there is a $q$-server doubly-efficient PIR scheme with exponent $\eta_{\mathcal L}$;
--   2. for every prime $q\equiv3\pmod4$ there is a $q$-server scheme with exponent $\eta_q$, the constant of (35);
--   3. $\eta_3<0.7897$, $\eta_7<0.7095$ and $\eta_{11}<0.6609$;
--   4. $\eta_q\le\frac12+\frac{0.467+o(1)}{\log_2q}$ as $q\to\infty$ along primes $q\equiv3\pmod4$;
--   5. as $s\to\infty$, there are $s$-server schemes with exponent $\frac12+\frac{0.467+o(1)}{\log_2 s}$.
--
--   A scheme with exponent $\rho$ is as in Definition 5.1 (see Main Theorem 5.2). This is the lattice track: the schemes come from the cone-delta functions of Theorem 11.9, whose support $S_d$ has size $q^{(\eta_{\mathcal L}+o(1))d}$.
--
--   **Formalization Note** The lattice is $B\mathbb Z^r$, over all $r$ and all $B$ with `IsEvenLatticeDetSqrt q B` ($r$ even and positive, $B$ of full rank, the lattice even, $|\det B|=\sqrt q$); $\eta_{\mathcal L}$ is `etaL q B` and $\eta_q$ is `etaQ q`. Each $o(1)$ is one function $h$ with $h\to0$.
--
--   Differences from the source:
--   - reading: an s-server (q-server) scheme with exponent ρ → the base mission's `ModFormPIR.HasScheme s ρ` (Definition 5.1: one finite program triple on the base word RAM with bit probes, n + 1 stored bits, O(log² n) upload, n·polylog preprocessing, expected polylog parameter sampling, and (n+1)^{ρ+g(n)} reads, steps and answer bits with one g → 0); reason: same notion as the published goal Main Theorem 5.5
--   - encoding: η_q ≤ 1/2 + (0.467 + o(1))/log₂ q as q → ∞ (along primes q ≡ 3 mod 4) → ∃ h : ℕ → ℝ, h → 0, with etaQ q ≤ 1/2 + (0.467 + h q)/log₂ q for every prime q ≡ 3 (mod 4); reason: the values of h off those primes are free, so this is the o(1) statement; same encoding as the published Main Theorem 5.5
--   - encoding: as s → ∞, s-server schemes with exponent 1/2 + (0.467 + o(1))/log₂ s → ∃ h → 0 with HasScheme s (1/2 + (0.467 + h s)/log₂ s) for every s ≥ 3; reason: the proof (Appendix A) starts from 'given s ≥ 3'; finitely many s are absorbed by h; same encoding as Main Theorem 5.5
--   - encoding: an even lattice ℒ ⊆ ℝ^r of determinant √q (with Definition 11.1: r even positive, B of full rank) → ℒ(B) = Bℤ^r for B : Matrix (Fin r) (Fin r) ℝ with IsEvenLatticeDetSqrt q B; ℒ*/ℒ as the quotient of ℒ* by ℒ ∩ ℒ*; reason: every lattice of Definition 11.1 is Bℤ^r for a basis matrix B, and ℒ ⊆ ℒ* for an even lattice
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Main Theorem 5.3, p.21 (PDF p.25); (34), p.53 (PDF p.57); (35), p.54 (PDF p.58); proof in Appendix A, pp.88–89 (PDF pp.92–93)

import Mathlib
import Definitions.Def_ModFormPIR_Scheme
import Definitions.Def_ModFormPIR_Supplement_Lattice

open Filter Topology

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-- **Main Theorem 5.3** (Track 2: theta functions of lattices), p.21 (PDF p.25). Henzinger, Ragavan,
*Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256
2442f3db…). For an odd prime `q` and an even lattice `ℒ ⊆ ℝ^r` of determinant `√q`, there is a `q`-server
scheme with exponent `η_ℒ`. For every prime `q ≡ 3 (mod 4)` there is a `q`-server scheme with exponent `η_q`
of (35); `η_3 < 0.7897`, `η_7 < 0.7095`, `η_11 < 0.6609`; `η_q ≤ 1/2 + (0.467 + o(1))/log₂ q` as `q → ∞`; and
as `s → ∞` there are `s`-server schemes with exponent `1/2 + (0.467 + o(1))/log₂ s`.

**Formalization Note.** A scheme with exponent `ρ` is the base mission's `ModFormPIR.HasScheme` (Definition 5.1).
The lattice is `ℒ(B) = Bℤ^r` for a real `r × r` matrix `B`, quantified over every `r` and `B` satisfying
`IsEvenLatticeDetSqrt q B`; `η_ℒ` (`etaL`) is computed from the discriminant group `ℒ*/ℒ` and depends on no
generator. Each `o(1)` is one function `h → 0`: along the primes `q ≡ 3 (mod 4)` for `η_q`, and for all
`s ≥ 3` for the schemes (the proof starts from "given `s ≥ 3`"; `3` is the least prime `≡ 3 (mod 4)`). -/
theorem main_theorem_5_3 :
    (∀ q : ℕ, q.Prime → Odd q → ∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℝ),
      IsEvenLatticeDetSqrt q B → HasScheme q (etaL q B)) ∧
    (∀ q : ℕ, q.Prime → q % 4 = 3 → HasScheme q (etaQ q)) ∧
    etaQ 3 < 0.7897 ∧ etaQ 7 < 0.7095 ∧ etaQ 11 < 0.6609 ∧
    (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧ ∀ q : ℕ, q.Prime → q % 4 = 3 →
      etaQ q ≤ 1 / 2 + (0.467 + h q) / Real.logb 2 q) ∧
    (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧ ∀ s : ℕ, 3 ≤ s →
      HasScheme s (1 / 2 + (0.467 + h s) / Real.logb 2 s)) := by sorry

end Supplement

end ModFormPIR
