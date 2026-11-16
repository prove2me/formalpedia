-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_22
-- name    : GeoQAC.Supplement.theorem_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:25:21.697211+00:00
-- url     : https://prove2.me/theorems/fd6022e3-e905-4c37-8e73-c258b0b02369
-- title:
--   Theorem 3.22 — 1D-QAC PARITY: success at most $1/2+81^d2^{-n}$, depth $\Omega(n)$
-- statement:
--   Let $C$ be a depth-$d$ 1D-QAC circuit (a $[1,h]$-2D-QAC circuit) whose $n$ input qubits occupy arbitrary positions on the line, whose other qubits start in an arbitrary input-independent density matrix $\sigma$ (possibly mixed or entangled), and whose designated output qubit is measured, giving $g_C(x)$. Then, for $x$ uniform on $\{0,1\}^n$,
--   $$
--   \Pr_{x,C}\big[g_C(x)=\mathrm{PARITY}_n(x)\big]\le\frac12+81^d\cdot2^{-n}.
--   $$
--   In particular there are $c>0$ and $N$ such that, for $n\ge N$, if $\Pr[g_C(x)=\mathrm{PARITY}_n(x)]\ge2/3$ for every input $x$, then $d\ge c\,n$.
--
--   In one dimension, interval gates of unbounded length do not help: PARITY needs linear depth even with bounded error.
--
--   Differences from the source:
--   - encoding: depth Ω(n) → absolute c > 0 and threshold N with d ≥ c·n for n ≥ N; reason: asymptotic notation with an absolute constant (§2.1)
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.22, p.28

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_parityFn
import Definitions.Def_GeoQAC_Supplement_outProb

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.22** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.28). Setting of §3.7:
"the `n` classical input qubits may occupy arbitrary positions on the line, with any finite number
of ancillas in an input-independent state, possibly mixed or entangled. We measure one designated
output qubit and write `g_C(x)` for the resulting bit." Theorem: "For uniformly random
`x ∈ {0,1}^n`, every depth-`d` 1D-QAC circuit `C` in this setting satisfies
`Pr_{x,C}[g_C(x) = PARITY_n(x)] ≤ 1/2 + 81^d · 2^{−n}`. In particular, approximate computation of
PARITY, with success probability at least `2/3` on every input, requires depth `Ω(n)`."

**Formalization Note.**
* A 1D-QAC circuit is a `[1, h]`-2D-QAC circuit (Definition 2.3: width one). Inputs at any
  injective placement `inp`, output at any qubit `out`, ancilla state any density matrix `σ` on the
  non-input qubits (`outProb`, `avgSuccess`).
* The first clause holds for every `n, d, h`. The `Ω(n)` clause: absolute `c > 0` and threshold `N`
  such that for `n ≥ N` success probability `≥ 2/3` on every input forces `d ≥ c·n`. -/
theorem theorem_3_22 :
    (∀ (n d h : ℕ) (C : QACCircuit (Pos 1 h) d) (inp : Fin n ↪ Pos 1 h) (out : Pos 1 h)
      (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ),
      C.Is2D → IsDensityMatrix σ →
        avgSuccess C inp σ out (parityFn n) ≤ 1 / 2 + (81 : ℝ) ^ d / 2 ^ n) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (d h : ℕ) (C : QACCircuit (Pos 1 h) d) (inp : Fin n ↪ Pos 1 h) (out : Pos 1 h)
        (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ),
        C.Is2D → IsDensityMatrix σ →
        (∀ x : Fin n → Bool, 2 / 3 ≤ outProb C inp σ out x (parityFn n x)) →
          c * n ≤ d) := by sorry

end GeoQAC.Supplement
