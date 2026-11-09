-- Prove2me | Theorems.Thm_NKtLB_theorem_8
-- name    : NKtLB.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:17:10.11913+00:00
-- url     : https://prove2.me/theorems/76953026-70a9-4afc-a6f9-cc94576b7398
-- title:
--   Theorem 8 — complexity lower bounds for estimating nKt
-- statement:
--   1. There is a constant $\varepsilon>0$ such that
--   $$
--   \mathrm{MnKtP}\notin\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}].
--   $$
--   2. Moreover, for every constant $1/2<\gamma<1$ there is $\varepsilon=\varepsilon(\gamma)>0$ such that, for every dense language $L\subseteq R_{\mathrm{nKt}}[\gamma\cdot n]$,
--   $$
--   L\notin\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}].
--   $$
--
--   Previously only $\mathrm{MnKtP}\notin\mathsf{NP}\cap\mathsf{coNP}$ was known (Allender 2010; Allender, Koucký, Ronneburger, Roy 2011). The theorem gives an exponential lower bound. More generally, it shows that distinguishing strings of bounded nondeterministic complexity from random strings is hard.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - reading: $U$ runs in time $\tilde O(|M|,t)$ → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$, with queries passed through; reason: quasi-linear overhead is what Eq. (30) needs; the additive $c_M$ covers $t\le1$
--   - reading: $\mathsf{NTIME}[2^{\varepsilon n}]$ → time $c\lceil2^{\varepsilon n}\rceil+c$ for some $c$ (`NTIME (expBound ε)`); reason: the standard class with $O(T)$ time; the larger class makes the lower bound stronger
--   - encoding: $R_{\mathrm{nKt}[s]}$ for $s:\mathbb N\to\mathbb N$ → $s:\mathbb N\to\mathbb R$; reason: the paper uses $s(n)=\gamma n$; integer-valued $s$ give the paper's set
--   - reading: "dense": a positive constant $b$ → a real $b>0$, density eventually in $n$; reason: the definition on p.12
--   - encoding: the instance $(x,1^s)$ → the string $\mathrm{dbl}(x)\,01\,1^s$ (`pairEnc`); reason: the paper fixes no pairing; this one is injective, of linear length, and easy to decode
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 8, p.12 (proof pp.74–77)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_MnKtP
import Definitions.Def_NKtLB_RnKt
import Definitions.Def_NKtLB_Dense
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_expBound

namespace NKtLB

/-- **Theorem 8 (Complexity Lower Bounds for Estimating nKt)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 8, p.12): "There is a
constant `ε > 0` such that `MnKtP ∉ NTIME[2^{εn}] ∩ coNTIME[2^{εn}]`. Moreover, given a constant
`1/2 < γ < 1`, there exists `ε = ε(γ) > 0` such that, for every dense language `L ⊆ R_{nKt[γ·n]}`, we
have `L ∉ NTIME[2^{εn}] ∩ coNTIME[2^{εn}]`."

**Formalization Note.** For every valid universal machine `U` (readings R1, R2); `MnKtP` is the
language of encodings `pairEnc x s` with `nKt(x) ≤ s` (R6); `NTIME[2^{εn}]` is time `O(2^{εn})`
(R3); dense with a real `b > 0` (R7). -/
theorem theorem_8 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    (∃ ε : ℝ, 0 < ε ∧ MnKtP U ∉ NTIME (expBound ε) ∩ coNTIME (expBound ε)) ∧
    (∀ γ : ℝ, 1 / 2 < γ → γ < 1 → ∃ ε : ℝ, 0 < ε ∧ ∀ L : Set (List Bool), Dense L →
      L ⊆ RnKt U (fun n => γ * n) → L ∉ NTIME (expBound ε) ∩ coNTIME (expBound ε)) := by sorry

end NKtLB
