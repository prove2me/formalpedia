-- Prove2me | Theorems.Thm_MixedCloning_Optimal_werner_trace_bose
-- name    : MixedCloning.Optimal.werner_trace_bose
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T03:08:20.331097+00:00
-- url     : https://prove2.me/theorems/ed5ddcfc-2f59-4793-b37e-a7d53e587347
-- title:
--   Werner's cloner is trace preserving on the Bose sector
-- statement:
--   Let $a$ be a finite set with $D=|a|$ elements and let $n,k\ge0$. Write $\Pi_j$ for the orthogonal projector onto the symmetric subspace of $(\mathbb C^a)^{\otimes j}$, the average of the $j!$ permutation operators, and $d[j]=\binom{j+D-1}{j}$ for its dimension. For every matrix $X$ on $(\mathbb C^a)^{\otimes n}$, put $\rho=\Pi_nX\Pi_n$. Then
--
--   $$
--   d[n]\;\operatorname{tr}\Big(\Pi_{n+k}\big(\rho\otimes I^{\otimes k}\big)\Pi_{n+k}\Big)\;=\;d[n+k]\;\operatorname{tr}\rho .
--   $$
--
--   Equivalently, when $D\ge1$, Werner's cloning map
--
--   $$
--   T(\rho)=\frac{d[n]}{d[n+k]}\,\Pi_{n+k}\big(\rho\otimes I^{\otimes k}\big)\Pi_{n+k}
--   $$
--
--   preserves the trace of every operator supported on the symmetric subspace.
--
--   This is Werner's check that the normalization of his cloner makes it trace preserving. It supplies the trace-one property of Werner's output in the bridge to Lemma 7 of the mixed-state cloning source, and it is the trace-preservation part of the PCT channel property.
--
--   **Formalization Note** $\Pi_j$ is the platform function `symProjector a j`, the normalized sum of the permutation matrices `permMatrix`. The map $\rho\mapsto\rho\otimes I^{\otimes k}$ is `appendIdentity n k`, which places the $k$ identity factors on the last registers. The identity is stated multiplied out, without division.
--
--   Differences from the source:
--   - encoding: density matrices on the Bose sector → $\rho=\Pi_nX\Pi_n$ for an arbitrary matrix $X$; reason: these are exactly the operators supported on the symmetric subspace, and both sides are linear in $\rho$
--   - encoding: $\operatorname{tr}T(\rho)=\operatorname{tr}\rho$ → the cross-multiplied identity; reason: it avoids division and remains meaningful when $D=0$
--   - generalization: $M>N$ → $M=N+k$ with $k\ge0$; reason: the case $k=0$ is the trivial identity $\operatorname{tr}(\Pi_n\rho\Pi_n)=\operatorname{tr}\rho$
-- source:
--   R. F. Werner, Optimal cloning of pure states, Phys. Rev. A 58, 1827 (1998), arXiv:quant-ph/9804001, PDF p. 6: Eq. (3.3) and the paragraph following it, where the normalization of the cloning map is shown to make it trace preserving on the Bose sector; used for Lemma 7 in D. Grinko, M. Fanizza, T. Scharnhorst, J. Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243, p. 11.

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Werner [Wer98], arXiv:quant-ph/9804001 p.6, Eq. (3.3) and the paragraph after it: the cloner
`T(ρ) = (d[N]/d[M]) s_M (ρ ⊗ 1^{⊗(M-N)}) s_M` is trace preserving on the Bose sector. Stated
multiplied out (no division), for `ρ = Π_n X Π_n` with an arbitrary matrix `X`. -/
theorem werner_trace_bose {a : Type} [Fintype a] (n k : ℕ) (X : Op (Word a n)) :
    (symDimension (Fintype.card a) n : ℂ) *
        (symProjector a (n+k) * appendIdentity n k (symProjector a n * X * symProjector a n) *
          symProjector a (n+k)).trace =
      (symDimension (Fintype.card a) (n+k) : ℂ) *
        (symProjector a n * X * symProjector a n).trace := by sorry

end MixedCloning.Optimal
