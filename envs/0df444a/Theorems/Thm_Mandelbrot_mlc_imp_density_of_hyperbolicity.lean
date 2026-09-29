-- Prove2me | Theorems.Thm_Mandelbrot_mlc_imp_density_of_hyperbolicity
-- name    : Mandelbrot.mlc_imp_density_of_hyperbolicity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:10:11.607577+00:00
-- url     : https://prove2.me/theorems/33b2b5a6-cf70-40c2-a8ac-0aa538e5b49c
-- title:
--   MLC implies density of hyperbolicity in the quadratic family
-- statement:
--   **Theorem (Douady-Hubbard).** If the Mandelbrot set is locally connected, then hyperbolic parameters are dense in it: every $c \in M$ is a limit of parameters $c'$ for which $z \mapsto z^{2} + c'$ has an attracting cycle.
--
--   This implication is a principal reason for the central place of MLC. Combined with the elementary density of hyperbolic parameters outside $M$, it would settle the *density of hyperbolicity conjecture* -- Fatou's conjecture for the quadratic family -- which asserts that hyperbolic maps are dense in the whole family $\{z^{2} + c\}$. The argument passes through the combinatorial rigidity supplied by the pinched-disk model: local connectivity of $M$ yields rigidity, and rigidity forces every non-hyperbolic parameter to be approximated by hyperbolic ones.
-- source:
--   A. Douady and J. H. Hubbard, Etude dynamique des polynomes complexes, Orsay notes 1984/85 ; https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Douady-Hubbard**: if the Mandelbrot set is locally connected, then the parameters
with an attracting cycle are dense in it. -/
theorem mlc_imp_density_of_hyperbolicity (h : LocallyConnectedSpace mandelbrotSet) :
    mandelbrotSet ⊆ closure {c : ℂ | ∃ m z, IsAttractingCycle (fun z ↦ z ^ 2 + c) m z} := by
  sorry

end Mandelbrot
