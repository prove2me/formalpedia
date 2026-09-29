-- Prove2me | Theorems.Thm_ModularCurve_ssCountFormula_eq_genus
-- name    : ModularCurve.ssCountFormula_eq_genus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/678bfce4-d13c-5286-a51e-0a785872418b
-- title:
--   Supersingular count formula equals genus defect g(Nq)-2g(N)+1
-- statement:
--   Let $N$ and $q$ be natural numbers with $N \neq 0$, let $q$ be prime, and assume $q \nmid N$. Write $\psi(M) = \sum_{d \mid M,\ d \text{ squarefree}} M/d$ for the arithmetic function `dedekindPsi`, $\nu_2(M)$ for the number of $x \in \mathbb{Z}/M$ with $x^2 + 1 = 0$, $\nu_3(M)$ for the number of $x \in \mathbb{Z}/M$ with $x^2 + x + 1 = 0$, and $\nu_\infty(M) = \sum_{d \mid M} \varphi(\gcd(d, M/d))$ for `cuspCount`. The rational number `ssCountFormula N q` is by definition the Eichler mass $(q-1)\psi(N)/12$ together with the two correction terms $(2-\nu_2(q))\nu_2(N)/4$ and $(2-\nu_3(q))\nu_3(N)/3$, and `genusFormula M` is $1 + \psi(M)/12 - \nu_2(M)/4 - \nu_3(M)/3 - \nu_\infty(M)/2$. The theorem asserts the identity of rational numbers
--   $$\frac{(q-1)\psi(N)}{12} + \frac{(2-\nu_2(q))\nu_2(N)}{4} + \frac{(2-\nu_3(q))\nu_3(N)}{3} = \mathrm{genusFormula}(Nq) - 2\,\mathrm{genusFormula}(N) + 1 .$$
--   This is a statement purely about these arithmetic functions; no modular curve or supersingular locus occurs in it.
--
--   The left-hand side is the Eichler–Deuring closed form for the number of supersingular points in characteristic $q$ on the modular curve of level $N$, and the right-hand side is the genus defect predicted by the Deligne–Rapoport description of the fibre of $X_0(Nq)$ at $q$ as two copies of $X_0(N)$ crossing at the supersingular points. The identity is used in the comparison of the genus of the reduced modular function field with the set of supersingular places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssCountFormula_eq_genus.lean

import Mathlib
import Definitions.Def_ModularCurve_EichlerMass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve

theorem ssCountFormula_eq_genus {N q : ℕ} (hN : N ≠ 0) (hq : q.Prime)
    (hqN : ¬ q ∣ N) :
    ssCountFormula N q = genusFormula (N * q) - 2 * genusFormula N + 1 := by sorry
