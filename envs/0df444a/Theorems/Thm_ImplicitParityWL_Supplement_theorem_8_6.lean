-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_8_6
-- name    : ImplicitParityWL.Supplement.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:31:00.474424+00:00
-- url     : https://prove2.me/theorems/ca876657-424c-4450-b101-504c48308b4f
-- title:
--   Theorem 8.6 — compiling register programs to $(s+1)$-WL instances
-- statement:
--   Let $R$ be a register program with $s\ge2$ registers over $A=\mathbb F_2^\ell$ ($\ell\ge1$), $w$ control locations and $r$ guarded commands, let $(p^*,a^*)$ be a query, put $Q=2^\ell$, and let $L$ be the bit length of the encoding of $R$ and the query (§8.4). Then $R$ and the query compile to colored graphs $\tilde G_0,\tilde G_1$ such that
--   $$\text{the query accepts}\iff(s+1)\text{-WL distinguishes }\tilde G_0,\tilde G_1.$$
--   Their total order $N$ and total edge count $E$ satisfy
--   $$N+E=O\bigl(sQw+s^2Q\ell r\bigr)\tag{24}$$
--   with an absolute constant. The construction takes time $O((L+sQw+s^2Q\ell r)^c)$ for an absolute constant $c$, and, for fixed $s$, time
--   $$\tilde O_s\bigl(L+Q(w+r)\bigr)\tag{25}$$
--   on a deterministic multitape Turing machine, where the suppressed factor is a fixed absolute power of the logarithm.
--
--   Theorem 8.6 is the interface through which Turing machines are turned into WL instances: it yields the hardness results 1.1, 1.2 and 9.2.
--
--   **Formalization Note** One machine does everything: on every encoding of $R$ and the query (each guard set given by its elements or by its membership string), it halts with the codes of $\tilde G_0$ and $\tilde G_1$ on its tape within $\lfloor C(L+sQw+s^2Q\ell r)^c\rfloor$ and within $\lfloor C_s\,X\,(\log_2(X+2))^a\rfloor$ steps, $X=L+Q(w+r)$, where $C$, $c$ and $a$ are absolute and $C_s$ depends on $s$ alone; the same $C$ bounds (24). The graphs have vertices $0,\dots,N_\varepsilon-1$ and colors in $\mathbb N$, and "distinguishes" means that the round-$t$ histograms differ for some $t$.
--
--   Differences from the source:
--   - reading: the graphs can be constructed in polynomial time, and for fixed s in time Õ_s(L + Q(w + r)) → one machine meeting both time bounds and the size bound for every s ≥ 2; reason: the stronger reading; the construction of the proof is uniform in s
--   - generalization: a finite set of guarded commands at each location → one list of commands, each carrying its location; repetitions allowed and counted in r; reason: a repeated command changes no acceptance; on repetition-free lists this is the source's statement
--   - encoding: encoding of §8.4 (content fixed, bit layout not) → Encodes: self-delimiting integerCode numbers, tagged commands, each guard set in either allowed form; reason: the page fixes the content of the encoding, not its layout
--   - encoding: Õ_s(L + Q(w + r)) with an absolute log power → ⌊C_s · X · (log₂(X + 2))^a⌋₊, X = L + Q(w + r), a absolute; reason: the paper's own argument log(H + S + 2) in Lemma 7.2
--   - encoding: colored graphs output by the construction → the word coloredCode G̃₀ ++ coloredCode G̃₁ of graphs on Fin N₀, Fin N₁ with colors in ℕ; reason: the vertex and edge records of Lemma 7.2
--   - encoding: control locations P with accept, reject ∈ P → RegisterProgram with locations Fin w and a field accept ≠ reject; reason: Definition 8.1 halts and accepts at accept and halts and rejects at reject, so the two locations are distinct on the page; no program of the page is excluded
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 8.6 and eqs. (24), (25), pp.47–48; encoding §8.4, p.47

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_ImplicitParityWL_WLColor
import Definitions.Def_ImplicitParityWL_Supplement_Codes
import Definitions.Def_ImplicitParityWL_Supplement_RegisterProgram

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- **Theorem 8.6** (Compiling register programs; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for
the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, pp.47–48):
a register program `R` with `s ≥ 2` registers over `A = 𝔽₂^ℓ`, `w` control locations, `r` guarded
commands, and a query `(p∗, a∗)` compiles to colored graphs `G̃₀`, `G̃₁` such that the query accepts iff
`(s + 1)`-WL distinguishes `G̃₀`, `G̃₁`. Their total order `N` and total edge count `E` satisfy
`N + E = O(sQw + s²Qℓr)` (24), `Q = 2^ℓ`, with an absolute constant. Construction takes time
`O((L + sQw + s²Qℓr)^c)` for an absolute `c`. For fixed `s`, both graphs can be constructed in time
`Õ_s(L + Q(w + r))` (25) on a deterministic multitape Turing machine, the suppressed factor being a
fixed absolute power of the logarithm.

**Formalization Note** One machine `M` (the published `OAI.VariableWL.Machine`) does all of it: on every
encoding `u` of `R` and the query in the sense of §8.4 (`Encodes`; each guard set listed by elements or
as a membership string), it halts with `coloredCode G̃₀ ++ coloredCode G̃₁` on tape `0`, within both time
bounds. `L = |u|`, `w = R.w`, `r = R.cmds.length`. `C`, `c` and the log power `a` are absolute (chosen
before `s`); `C_s` depends on `s` alone. The log is `log₂(L + Q(w + r) + 2)`. "Distinguishes" is
`DistinguishesAfter` at some round, for the decoded colored graphs on `Fin N₀`, `Fin N₁` with colors in
`ℕ`. -/
theorem theorem_8_6 : ∃ (C c a : ℕ) (M : Machine), ∀ s : ℕ, 2 ≤ s → ∃ Cs : ℝ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ (R : RegisterProgram s ℓ) (p : Fin R.w) (a₀ : Fin s → RegVal ℓ) (u : Word),
      Encodes R p a₀ u →
      ∃ (N₀ N₁ : ℕ) (G₀ : ColoredGraph ℕ (Fin N₀)) (G₁ : ColoredGraph ℕ (Fin N₁)),
        (R.Accepts p a₀ ↔ ∃ t : ℕ, DistinguishesAfter G₀ G₁ (s + 1) t) ∧
        N₀ + N₁ + edgeCount G₀ + edgeCount G₁ ≤
          C * (s * 2 ^ ℓ * R.w + s ^ 2 * 2 ^ ℓ * ℓ * R.cmds.length) ∧
        OutputsWithin M u (coloredCode G₀ ++ coloredCode G₁)
          (C * (u.length + s * 2 ^ ℓ * R.w + s ^ 2 * 2 ^ ℓ * ℓ * R.cmds.length) ^ c) ∧
        OutputsWithin M u (coloredCode G₀ ++ coloredCode G₁)
          ⌊Cs * ((u.length + 2 ^ ℓ * (R.w + R.cmds.length) : ℕ) : ℝ) *
            Real.logb 2 ((u.length + 2 ^ ℓ * (R.w + R.cmds.length) : ℕ) + 2 : ℝ) ^ a⌋₊ := by sorry

end Supplement

end ImplicitParityWL
