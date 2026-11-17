-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_5_4
-- name    : ModLatSVP.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:24:05.277028+00:00
-- url     : https://prove2.me/theorems/d9707a8c-b3d9-4f03-9dc5-04f94bfbdc52
-- title:
--   Theorem 5.4, p.35 — rank-$n$ modules over cyclotomic fields — exact CVP and all closest vectors in time $\mathrm{poly}_n\cdot d^{((n-1)/2+1/(2e))d+o(d)}$, polynomial space
-- statement:
--   Fix a module rank $n\ge1$. Let $K=\mathbb Q(\zeta_m)$ be a cyclotomic field of degree $d$ and $M\cong\mathbb Z^N$, $N=nd$, a rank-$n$ module over $K$ in the input model of §2.2. For every rational target $t$, a closest vector of $M$ to $t$, and the list of all closest vectors (each once), can be computed deterministically in time
--
--   $$(\ell+1)^{k}\,d^{\,\left(\frac{n-1}{2}+\frac{1}{2e}\right)d+g(d)}$$
--
--   and polynomial working space $(\ell+1)^{k'}$, where $\ell$ is the input length and $k,k'$ and the function $g$ with $g(d)/d\to0$ depend only on $n$.
--
--   No bound on the root discriminant is required: semistability of cyclotomic rank-one modules replaces it.
--
--   **Formalization Note** TM2 machines with the base mission's conventions; the cyclotomic field is $\texttt{IsCyclotomicExtension}\ \{m\}\ \mathbb Q\ K$ for some $m\ge1$, with $\star$ (complex conjugation) characterized by $\texttt{ModLatSVP.IsStar}$.
--
--   Differences from the source:
--   - reading: "can be solved in deterministic time … and polynomial working space" (no machine named) → deterministic TM2 machines, time SpikyCVP.RunsWithin, working space SpaceWithin bounded by (ℓ + 1)^{k'}; reason: same model as the published goal Theorem 1.1
--   - reading: poly_n(B, d, ℓ(t)) d^{((n−1)/2+1/(2e))d+o(d)} → ⌊(ℓ + 1)^k d^{((n−1)/2 + 1/(2e))d + g(d)}⌋ steps, k and g (g(d)/d → 0) depending only on n; reason: B, d, ℓ(t) ≤ ℓ; o(d) as an explicit function
--   - encoding: exact CVP and enumeration of all closest vectors → one machine outputting a closest vector, one outputting a duplicate-free list of exactly the closest vectors; reason: both tasks of the statement
--   - encoding: cyclotomic field K of degree d; module in the input model of Section 2.2 → IsCyclotomicExtension {m} ℚ K for some m ≥ 1; module input with RepresentsField, RepresentsModule, IsStar, N = n·d; reason: Mathlib's cyclotomic extensions; the base mission's input model
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 5.4, p.35 (PDF p.35); input model §2.2, p.12

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField Filter Topology

namespace ModLatSVP

namespace Supplement

/-- **Theorem 5.4, §5.4, p.35: CVP on higher-rank cyclotomic modules.** Kim, Lee, Son, *Exact SVP and CVP
in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "Fix n ≥ 1. Let M be a rank-n module over a cyclotomic field K of degree d, in the
input model of Section 2.2. For every rational target t, exact CVP and enumeration of all closest vectors
can be solved in deterministic time poly_n(B, d, ℓ(t)) d^{((n−1)/2+1/(2e))d+o(d)} and polynomial working
space."

Fix `n ≥ 1`. There are TM2 machines `M_CVP`, `M_all`, degrees `k, k'` and a function `g` with
`g(d)/d → 0` (all depending only on `n`) such that for every cyclotomic field `K = ℚ(ζ_m)` of degree `d`
with its involution `⋆`, every module input `(d, c, S, G, A)` of a rank-`n` module `ℤ^N`, `N = n d`, and
every rational target `t` (`ℓ` bits in all), `M_CVP` outputs one closest vector to `t` and `M_all` the list
of all closest vectors, each exactly once, each within `(ℓ + 1)^k d^{((n−1)/2 + 1/(2e)) d + g(d)}` steps and
working space `(ℓ + 1)^{k'}`.

**Formalization Note.**
* "Cyclotomic field" is `IsCyclotomicExtension {m} ℚ K` for some `m ≥ 1`; `⋆` is characterized by
  `ModLatSVP.IsStar` (complex conjugation). No root-discriminant hypothesis, as in the source.
* Machines, working space, outputs as in `ModLatSVP.theorem_1_1`; `poly_n` is `(ℓ + 1)^k` with `k`
  depending only on `n`; `+o(d)` is an explicit `g` with `g(d)/d → 0`, chosen with the machines. -/
theorem theorem_5_4 (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Mcvp Mall : Turing.TM2ComputableAux Bool Bool) (g : ℕ → ℝ) (k k' : ℕ),
      Tendsto (fun m : ℕ => g m / m) atTop (𝓝 0) ∧
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ) (t : Fin N → ℚ),
        (∃ m : ℕ, 1 ≤ m ∧ IsCyclotomicExtension {m} ℚ K) → IsStar K τ →
        RepresentsField K τ ω c S → RepresentsModule K τ ω G A → N = n * d →
        ((∃ x : Fin N → ℤ, IsClosest G t x ∧
            SpikyCVP.RunsWithin Mcvp (encModule d N c S G A ++ SpikyCVP.encVec t) (encIntVec x)
              ⌊(((encModule d N c S G A ++ SpikyCVP.encVec t).length : ℝ) + 1) ^ k *
                (d : ℝ) ^ ((((n : ℝ) - 1) / 2 + 1 / (2 * Real.exp 1)) * d + g d)⌋₊) ∧
          SpaceWithin Mcvp (encModule d N c S G A ++ SpikyCVP.encVec t)
            (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) ∧
        ((∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
            SpikyCVP.RunsWithin Mall (encModule d N c S G A ++ SpikyCVP.encVec t)
              (xs.flatMap encIntVec)
              ⌊(((encModule d N c S G A ++ SpikyCVP.encVec t).length : ℝ) + 1) ^ k *
                (d : ℝ) ^ ((((n : ℝ) - 1) / 2 + 1 / (2 * Real.exp 1)) * d + g d)⌋₊) ∧
          SpaceWithin Mall (encModule d N c S G A ++ SpikyCVP.encVec t)
            (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) := by sorry

end Supplement

end ModLatSVP
