-- Prove2me | Theorems.Thm_HILL_PRG_flat_conditional_leftover_hash
-- name    : HILL.PRG.flat_conditional_leftover_hash
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T00:46:50.825715+00:00
-- url     : https://prove2.me/theorems/b75a91df-d6cf-4dae-8321-7851c572414c
-- title:
--   Conditional leftover hashing for flat fibers
-- statement:
--   Let $S$, $R$, and $Z$ be finite nonempty sets, and let $f$ be a deterministic map on $S$. Draw $X$ uniformly from $S$ and a key $K$ independently and uniformly from $R$. Suppose $h_K$ maps $S$ into $Z$, and for each two distinct seeds its probability of collision is at most $1/|Z|$. Let $U_Z$ be independently uniform on $Z$. For any threshold $L>0$,
--
--   $$
--   \Delta\bigl((f(X),K,h_K(X)),(f(X),K,U_Z)\bigr)
--   \ \le\
--   \Pr\bigl[|\{u\in S:f(u)=f(X)\}|<L\bigr]
--   +\frac12\sqrt{\frac{|Z|}{L}}.
--   $$
--
--   Here $\Delta$ denotes total variation distance. This is the finite conditional hashing estimate used in the extraction step of HILL Construction 4.15 and Lemma 4.16.
-- source:
--   Håstad, Impagliazzo, Levin, and Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, Lemma 4.8 and §4.7, pp. 1378–1381. https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf

import Definitions.Def_HILL_PRG_Model
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

open HILL.PRG
open scoped BigOperators

namespace HILL.PRG

theorem flat_conditional_leftover_hash {α β κ ζ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq κ] [DecidableEq ζ]
    (S : Finset α) (R : Finset κ) (Z : Finset ζ) (f : α → β) (h : κ → α → ζ)
    (hS : S.Nonempty) (hR : R.Nonempty) (hZ : Z.Nonempty)
    (hmap : ∀ r ∈ R, ∀ x ∈ S, h r x ∈ Z)
    (hcoll : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' →
      (Z.card : ℝ) * ((R.filter (fun r => h r x = h r x')).card : ℝ) ≤ (R.card : ℝ))
    (L : ℝ) (hL : 0 < L) :
    statDistOn ((S.image f) ×ˢ (R ×ˢ Z))
      (lawOn (S ×ˢ R) (fun xr => (f xr.1, (xr.2, h xr.2 xr.1))))
      (lawOn ((S ×ˢ R) ×ˢ Z) (fun xrz => (f xrz.1.1, (xrz.1.2, xrz.2))))
      ≤ (by
          classical
          exact uniformProb S (fun x => ((S.filter (fun u => f u = f x)).card : ℝ) < L)) +
        (1 / 2 : ℝ) * Real.sqrt ((Z.card : ℝ) / L) := by sorry

end HILL.PRG
