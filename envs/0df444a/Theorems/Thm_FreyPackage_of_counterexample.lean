-- Prove2me | Theorems.Thm_FreyPackage_of_counterexample
-- name    : FreyPackage.of_counterexample
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1ac53ab9-52e8-5256-a1c7-1d3759083e05
-- title:
--   Frey package from a counterexample of exponent p ≥ 5
-- statement:
--   Let $a, b, c$ be integers, each assumed nonzero, let $p$ be a natural number that is prime with $5 \le p$, and suppose $a^p + b^p = c^p$. The conclusion is that the type [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17) is nonempty, i.e. that some Frey package exists. Here [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17) is the project's own structure (not a Mathlib notion) whose data are three integers $a, b, c$ together with a natural number $p$, and whose fields are exactly: $a \ne 0$, $b \ne 0$, $c \ne 0$; $p$ prime and $5 \le p$; the equation $a^p + b^p = c^p$; the normalisation $\gcd(a,b) = 1$ (as an equality of integers, i.e. the integer cast of `Int.gcd`); the congruence condition expressed as $(a : \mathbb{Z}/4) = 3$; and the parity condition expressed as $(b : \mathbb{Z}/2) = 0$, that is $2 \mid b$. The structure carries no further fields; the coprimality of $a$ with $c$ and of $b$ with $c$, the oddness of $p$, and the Frey curve $y^2 + xy = x^3 + \frac{b^p - 1 - a^p}{4}x^2 - \frac{a^p b^p}{16}x$ over $\mathbb{Z}$ and over $\mathbb{Q}$ are defined or derived separately in the same module. Note that the conclusion is a bare nonemptiness assertion: it records no relation between the hypothesised triple $(a,b,c)$ and the exponent of the package produced, nor between the hypothesised $p$ and the package's $p$ (although the proof does keep the same $p$).
--
--   This is the elementary opening normalisation of the Frey–Hellegouarch–Serre–Ribet strategy: any putative counterexample to Fermat's Last Theorem with prime exponent $p \ge 5$ can be rescaled and sign-adjusted so that $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b$ is even, which is the data needed to write down an integral model of the Frey curve. Compared with the textbook formulation, the Lean statement discards all bookkeeping about which triple is produced and asserts only `Nonempty FreyPackage`, and its normalisation conditions are phrased as equalities in $\mathbb{Z}/4$ and $\mathbb{Z}/2$. It is used, together with [`FreyPackage.no_frey_package`](thm.html#FreyPackage.no_frey_package), as one of exactly two inputs to [`FreyPackage.fermatLastTheoremFor_of_five_le`](thm.html#FreyPackage.fermatLastTheoremFor_of_five_le), which deduces `FermatLastTheoremFor p` for every prime $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_of_counterexample.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.of_counterexample (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) : Nonempty FreyPackage := by sorry
